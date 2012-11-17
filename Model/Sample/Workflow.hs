module Model.Sample.Workflow where

import Data.Array
import Debug.Trace
import Control.Monad.State

import Model.Model
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

mWorkflow = snd $ runState (workflow' w1) emptyModel

solveAndShowWorkflow w = fst $ runState (workflow' w >> solveModel) emptyModel

workflow' :: Workflow -> ModelS ()
workflow' w = do
  let n  = fromIntegral $ length $ jobs w
      m = fromIntegral $ length $ machines w
      bigm = maximum $ elems $ durees w
      tmax = last $ temps w
      jobRange = [1..n]
      machineRange = [1..m] 
  
  [u] <- liftModelLP $ newVars 1
  rvars <- liftModelLP $ newVars $ n*m*(tmax + 1)
  xvars <- liftModelLP $ newVars $  n*m
  gamma <- liftModel $ ipNewIntegerVars  $ n*m
  gamma' <- liftModel $ ipNewIntegerVars $ n*m
  -- alpha <- liftModel $ ipNewIntegerVars $ n*m*(tmax + 1)
  -- alpha' <- liftModel $ ipNewIntegerVars $ n*m*(tmax + 1)
  let rTab = array ((1,1,0),(n,m,tmax)) $ zip [(i,j,k) | i <- jobRange, j <- machineRange, k <- temps w] rvars
      xTab = array ((1,1),(n,m)) $ zip [(i,j) | i <- jobRange, j <- machineRange] xvars
      gammaTab = array ((1,1),(n,m)) $ zip [(i,j) | i <- [1..n], j <- [1..m]] gamma
      gammaTab' = array ((1,1),(n,m)) $ zip [(i,j) | i <- [1..n], j <- [1..m]] gamma'
      -- alphaTab = array ((1,1,0),(n,m,tmax)) $ zip [(i,j,k) | i <- [1..n], j <- [1..m], k <- temps w] alpha
      -- alphaTab' = array ((1,1,0),(n,m,tmax)) $ zip [(i,j,k) | i <- [1..n], j <- [1..m], k <- temps w] alpha'
      -- u = max (xij)
      c1 :: [Constraint]
      c1 = do
        i <- jobRange
        j <- machineRange
        let xij  = xTab ! (i,j) 
            coeffs = (u,-1):(xij,1):[(rijt,1) | t <- temps w, let rijt = rTab ! (i,j,t)]
        [coeffs `LowerOrEqual` 0]
      
      -- précédences
      c2 :: [Constraint]
      c2 = do
        i <- jobRange
        j <- machineRange
        k <- machineRange
        let xij = xTab ! (i,j)
            dijk = dureesTransferts w ! (i,j,k)
            coeffs :: [CoeffList]
            coeffs = [(xij,1):(xok,-1):[(rijt,1) | t <- temps w, 
                                        let rijt = rTab ! (i,j,t)] 
                      | o <- successeurs w ! i, 
                        let xok = xTab ! (o,k)]
        map (\l -> l `LowerOrEqual` (- dijk)) coeffs
      c3 :: [Constraint]
      c3 = do
        i <- jobRange
        j <- machineRange
        let gammaij = gammaTab ! (i,j)
            gammaij' = gammaTab' ! (i,j)
            dij = durees w ! (i,j)
            ct1 = [(gammaij,1),(gammaij',-1)] `LowerOrEqual` 0
            ct2 = ((gammaij,1):[(rijt,-1) | t <- temps w,                                      
                                let rijt = rTab ! (i,j,t)]) `LowerOrEqual` 0
            ct3 = ((gammaij,-bigm):[(rijt,1) | t <- temps w,
                                    let rijt = rTab ! (i,j,t)]) `LowerOrEqual` 0
           
        [ct1,ct2,ct3]
      c3eq = [((gammaij',dij):[(rijt,-1) | t <- temps w,
                               let rijt = rTab ! (i,j,t)]) `Equal` 0 |              
              i <- jobRange,
              j <- machineRange,
              let gammaij' = gammaTab' ! (i,j)
                  dij = durees w ! (i,j)]
      c4 = [([(rijt,1) | j <- machineRange, t <- temps w, let rijt = rTab ! (i,j,t)]) `GreaterOrEqual` 1| i <- jobRange]       
      c5 = [ [(rijt,1) | i <- jobRange, let rijt = rTab ! (i,j,t)] `LowerOrEqual` 1 | j <- machineRange, t <- temps w]
      {-
      c6eq = do
        i <- jobRange
        j <- machineRange
        k <- take (fromInteger $ tmax - 1 - (truncate $ durees w ! (i,j))) $ temps w
        let alphaijk = alphaTab ! (i,j,k)
            alphaijk' =  alphaTab' ! (i,j,k)
            rijk = rTab ! (i,j,k)
            rijk' = if k == 0 then 0 else rTab ! (i,j,k-1)
            dij = durees w ! (i,j)
            ct1 = [(alphaijk,1), (rijk,-1) ,(rijk',1)] `Equal` 0
            ct2 = ((alphaijk', dij):[(rTab ! (i,j,k+l), -1) | l <- [0..(truncate dij - 1)]] ) `Equal` 0
        [ct1,ct2]
      c7 = [[(alphaTab ! (i,j,k), 1), (alphaTab' ! (i,j,k),-1)] `LowerOrEqual` 0 | i <- jobRange, 
                                                                                   j <- machineRange,
                                                                                   k <- temps w]
      -}
      cteq = c3eq -- ++ c6eq
      ctstr = c1 ++ c2 ++ c3 ++ c4 ++ c5 -- ++ c7
      nbCtrStr = fromIntegral $ length ctstr
      nbCtrEq = fromIntegral $ length cteq
      
  liftModelLP $ setObj Minimize [(u,1)]
  ctistr <- liftModelLP $ newCtrs nbCtrStr
  ctieq <- liftModelLP $ newCtrs $ nbCtrEq
  ctieq' <- liftModelLP $ newCtrs $ nbCtrEq
  liftModelLP $ foldM (\_ (ci,e) -> forceCtr [ci] e) [] $ zip ctistr ctstr
  liftModelLP $ foldM (\_ ((ci,ci'),e) -> forceCtr [ci,ci'] e) [] $ zip (zip ctieq ctieq') cteq
  
  setDVarName u "Z"
  foldM (\_ ((i,j),xij) -> setDVarName xij $ "X" ++ show i ++ show j) () (assocs xTab)                                                                                                                                           
  foldM (\_ ((i,j),gammaij) -> setDVarName gammaij $ "g" ++ show i ++ show j) () (assocs gammaTab)   
  foldM (\_ ((i,j),gammaij') -> setDVarName gammaij' $ "g'" ++ show i ++ show j) () (assocs gammaTab')   
  foldM (\_ ((i,j,k),rijk) -> setDVarName rijk $ "R" ++ show i ++ show j ++ show k ) () (assocs rTab)  
 -- foldM (\_ ((i,j,k),aijk) -> setDVarName aijk $ "a" ++ show i ++ show j ++ show k ) () (assocs alphaTab)  
 -- foldM (\_ ((i,j,k),aijk') -> setDVarName aijk' $ "a'" ++ show i ++ show j ++ show k ) () (assocs alphaTab')  
  liftModelLP please
  model <- get
  
  trace (concatMap (show' (getDVarMap model)) $ ctstr ++ cteq) $ return ()
  trace (concat ["int g" ++ show i ++ show j ++ ";\n"| i <- [1..n], j <- [1..m]]) $ return ()                                                                                                                                    
  trace (concat ["int g'" ++ show i ++ show j ++ ";\n"| i <- [1..n], j <- [1..m]]) $ return ()
 -- trace (concat ["bin a" ++ show i ++ show j ++ show k ++ ";\n"| i <- [1..n], j <- [1..m], k <- temps w]) $ return () 
 -- trace (concat ["bin a'" ++ show i ++ show j ++ show k ++ ";\n"| i <- [1..n], j <- [1..m], k <- temps w]) $ return () 
  trace (concat ["bin R" ++ show i ++ show j ++ show k ++ ";\n"| i <- [1..n], j <- [1..m], k <- temps w]) $ return () 
  return ()