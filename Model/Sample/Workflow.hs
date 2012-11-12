module Model.Sample.Workflow where

import Data.Array
import Control.Monad.State

import Solve.IP.IntegerPb
import Solve.LP.LinearPb
import Solve.LP.LPBuild

type Jobs = Integer
type Machine = Integer
data Workflow = Workflow { jobs :: [Jobs],
                           machines :: [Machine],
                           temps :: [Integer],
                           durees :: Array (Jobs,Machine) Double,
                           dureesTransferts :: Array (Jobs, Machine, Machine) Double,
                           successeurs :: Array Jobs [Jobs]}
           
transfertsT1 = [((1,1),0), ((1,2),2),
                ((2,1),3), ((2,2),0)]
transfertsT2 = [((1,1),0), ((1,2),2),
                ((2,1),1), ((2,2),0)]
transfertsT3 = [((1,1),0), ((1,2),4),
                ((2,1),3), ((2,2),0)]
w1 = Workflow {jobs = [1..3],
               machines = [1..2],
               temps = [0..12+14+10],
               durees = array ((1,1),(3,2)) [ ((1,1), 10),((1,2), 12), 
                                              ((2,1),  6), ((2,2),14),
                                              ((3,1),10), ((3,2),9)],
               dureesTransferts = array ((1,1,1),(3,2,2)) $
                                       [((1,j,k),val) | ((j,k),val) <- transfertsT1] ++
                                       [((2,j,k),val) | ((j,k),val) <- transfertsT2] ++
                                       [((3,j,k),val) | ((j,k),val) <- transfertsT3],
               successeurs = array (1,3) [(1,[2]), (2,[]), (3, [])]}

{- Overflow à l'écriture -}
workflow :: Workflow -> IntegerPbS ()
workflow w = do
  let n = fromIntegral $ length $ jobs w
      m = fromIntegral $ length $ machines w
      tmax = fromIntegral $ (length $ temps w) - 1
  -- Allocation des variables
  dvars <- liftIP $ newVars $ fromIntegral n
  yvars <- liftIP $ newVars $ fromIntegral $ n*m
  xvars <- liftIP $ newVars $ fromIntegral $ n*m
  rvars <- liftIP $ newVars $ fromIntegral $ n*m*(tmax+1)
  [u] <- liftIP $ newVars 1
  
  let  -- On crée un tableau qui associe la variable de décision aux chaques triplets r(i,j,k) 
    rTab = array ( (1,1,0),(n,m,tmax)) $ zip [(i,j,k) | i <- [1..n], j <- [1..m], k <- [0..tmax]] rvars
    dTab = array (1,n) $ zip [1..n] dvars
    yTab = array ((1,1), (n,m)) $ zip [(i,j) | i <- [1..n], j <- [1..m]] yvars
    xTab = array ((1,1), (n,m)) $ zip [(i,j) | i <- [1..n], j <- [1..m]] xvars
  -- min u
  liftIP $ setObj Minimize $ [(u,1)]
   
  -- (0) sc u >= xij + di quelque soit i,j
  let ctrsMax = [ [(xij,1),(u,-1)] `LowerOrEqual` (-dij) |
                   i <- [1..n],
                   j <- [1..m],
                   let xij = xTab ! (i,j)
                       dij = durees w ! (i,j)]
   -- (1) di = Somme ( y_i,j * d_i,j )
      ctrdi = [((di,1):[(yij,-dij) | j <- [1..m],
                        let dij = durees w ! (i,j)
                            yij = yTab ! (i,j)]) `LowerOrEqual` 0 | 
               i <- [1..n],
               let di = dTab ! ( i)]
              
  -- (2) y_ij = max (r_i_j_t )sur t
  --Pour tout i , j, yij est superieur à r_ijt, pour tout t
{-      ctrYR = [ [(yij, -1), (rijt, 1)] `LowerOrEqual` 0 | i <- [1..n],
                                                          j <- [1..m],
                                                          t <- [1..tmax],
                                                          let yij = yTab ! (i,j)
                                                              rijt = rTab ! (i,j,t)]
  -}            
      ctrYR = [((yij,1):[(rijt,-1/dij) | t <- [0..tmax], 
                                        let rijt = rTab ! (i,j,t)]) `Equal` 0 
                | i <- [1..n],
                  j <- [1..m],
                  let yij = yTab ! (i,j)
                      dij = durees w ! (i,j)]
  --(3) Somme_ j (y_i,j)=1 pour tout i
      ctrY = [ [(yij,1) | j <- [1..m],
                          let yij = yTab ! (i,j)] `Equal` 1 
             | i <- [1..n]]
             
  -- (4) xij + di + Dijk <= xok pour tout successeur o de i, machine disponnible k
      ctrPert = [ [(xij,1),(di,1),(xok,-1)]  `LowerOrEqual` (- (dureesTransferts w ! (i,j,k))) |   
                                   i <- [1..n],
                                   j <- [1..m],
                                   k <- [1..m],
                                   o <- successeurs w ! i,
                                   let xij = xTab ! (i,j)
                                       di = dTab ! i
                                       xok = xTab ! (o,k)]
  -- (5') : somme(r_i,j,k)_j,k = di , pour tout i 
      ctrEx = [ ((di, -1):[(rijk,1) |  
                          j <- [1..m],
                          k <- [0..tmax],
                          let rijk = rTab ! (i,j,k)]) `Equal` 0 
              | i <- [1..n], 
                let di = dTab ! i]
  
{-
  (5'') : SI {r_i,j,k = 1 ET r_i,j,(k-1) = 0} ALORS r_i,j,t = 1 pour t dans [k, k+dij]             
          pour tout k : gammaijk * dij <= somme [ rijt | t <- [k, k+ dij -1]] <= M*gamma ijk
          pour tout i, pour tout j, pour tout k : r_i,j,k+ r_i,j,k-1- gamma i,j,k <= 1
-}
{-----
 Il faut forcer la consécutivité et l'execution sur la meme machine
 
 Exectution sur la meme machine
 pour tout i, j
 SI somme _t (r_i,j,t) >=1 Alors  somme _t (r_i,j,t)=d_i,j

gamma_ij = 1 sSi somme_t rijt >= 1
gamma'_ij = 1 => somme _t rijt = dij

somme_t rijt >=1 => gamma_ij = 1
1*gamma_ij <= somme_t_rijt  <= M.gamma_ij

gamma_ij' =1 => somme_t rijt = dij
gamma_ij' * dij <= somme_t rij

gamma_ij =1 => gamma'_ij = 1
gamma_ij <= gamùa'_ij


MEMO : Essayer de chercher une CNS pour que cette condition suffise à contraindre la consécutivité.
-----}
      nbGamma = n*m
  gamma <-ipNewIntegerVars  nbGamma
  gamma' <- ipNewIntegerVars nbGamma
  let  gammaTab =  array ((1,1),(n,m)) $ zip [(i,j) | i <- [1..n], j <- [1..m]] gamma
       gammaTab' =  array ((1,1),(n,m)) $ zip [(i,j) | i <- [1..n], j <- [1..m]] gamma'
       {-somme_t rijt >=1 => gamma_ij = 1                                                                                                                                                                                        
         1*gamma_ij <= somme_t_rijt  <= M.gamma_ij  -}
       ctrGamma1 = do
         i <- [1..n]
         j <- [1..m]
         let gammaij = gammaTab ! (i,j) 
             gammaij' = gammaTab' ! (i,j)
             sommerijt = [(rTab ! (i,j,t),1) | t <- [0..tmax]]
             sommeMrijt = [(rTab ! (i,j,t), -1) | t <- [0..tmax]]
             ct1 = ((gammaij,1):sommeMrijt) `LowerOrEqual` 0
             ct1' = ((gammaij,-infty):sommerijt) `LowerOrEqual` 0
             ct2 = ((gammaij',durees w ! (i,j)):sommeMrijt) `LowerOrEqual` 0
             ct3 = [(gammaij,1),(gammaij',-1)] `LowerOrEqual` 0
           
         return [ct1,ct1',ct2,ct3]
       {-ctrGamma = [ [[(gammaijk, -1),(rTab ! (i,j,k), 1), (rTab ! (i,j,k-1),1)]        
                                     `LowerOrEqual` 1,
                     ((gammaijk,dij):[(rijt,-1) | t <- [k.. k+(truncate dij)],
                                                 let rijt = rTab ! (i,j,t) 
                                                     dij = durees w ! (i,j)  ] )    
                                      `LowerOrEqual`  0 ,
                     ((gammaijk, -infty):[(rijt,1) | t <- [k.. k+ truncate dij],
                                                    let rijt = rTab ! (i,j,t) 
                                                        dij = durees w ! (i,j)  ] )  
                                        `LowerOrEqual` 0 ]
                  |i <- [1..n],
                   j <- [1..m],
                   k <- [1..tmax -1],
                   let gammaijk = gammaTab ! (i,j,k)
                       dij = durees w ! (i,j)]-} 
       --ctrYR = []
       --ctrEx = []
       ctrGamma = ctrGamma1
       ctrTot1 = ctrsMax ++ ctrdi ++ ctrPert ++ concat ctrGamma
       ctrTot2 = ctrY ++ ctrEx ++ ctrYR
  contraintes <- liftIP $ newCtrs $ fromIntegral $ length $ ctrTot1
  contraintesEx <- liftIP $ newCtrs $ fromIntegral $ length $ ctrTot2
  foldM (\_ (ci,ct) -> liftIP $ forceCtr ci ct) [] $ zip contraintes ctrTot1
  foldM (\_ (ci,ct) -> liftIP $ addConstraint ci ct) Nothing $ zip contraintesEx ctrTot2
  return () 
