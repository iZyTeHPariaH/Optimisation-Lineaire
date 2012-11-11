module Model.Sample.Workflow where

import Data.Array
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
                
workflow :: Workflow -> IntegerPbS ()
workflow w = do
  let n = fromIntegral $ length $ jobs w
      m = fromIntegral $ length $ machines w
      tmax = fromIntegral $ length $ temps w
  -- Allocation des variables
  dvars <- liftIP $ newVars $ fromIntegral n
  yvars <- liftIP $ newVars $ fromIntegral $ n*m
  xvars <- liftIP $ newVars $ fromIntegral $ n*m
  rvars <- liftIP $ newVars $ fromIntegral $ n*m*tmax
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
      ctrYR = [ [(yij, -1), (rijt, 1)] `LowerOrEqual` 0 | i <- [1..n],
                                                          j <- [1..m],
                                                          t <- [1..tmax],
                                                          let yij = yTab ! (i,j)
                                                              rijt = rTab ! (i,j,t)]
              
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
                          k <- [1..tmax],
                          let rijk = rTab ! (i,j,k)]) `Equal` 0 
              | i <- [1..n], 
                let di = dTab ! i]
  
{-
  (5'') : SI {r_i,j,k = 1 ET r_i,j,(k-1) = 0} ALORS r_i,j,t = 1 pour t dans [k, k+dij]             
          pour tout k : gammaijk * dij <= somme [ rijt | t <- [k, k+ dij -1]] <= M*gamma ijk
          pour tout i, pour tout j, pour tout k : r_i,j,k+ r_i,j,k-1- gamma i,j,k <= 1
-}
      nbGamma = sum [fromInteger tmax - dij +1 | i <- [1..n], j <- [1..m], let dij = durees w ! (i,j)]
  gamma <-ipNewIntegerVars $ truncate nbGamma
  
  let  gammaTab = array ((1,1,0), (n,m,tmax -1)) $ 
                  zip [(i,j,k) | i <- [1..n], j <- [1..m], k <- [0..tmax]] gamma
       ctrGamma = [ [[(gammaijk, -1),(rTab ! (i,j,k), 1), (rTab ! (i,j,k-1),1)]        
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
                       dij = durees w ! (i,j)] 
  return ()