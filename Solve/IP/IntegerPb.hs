module Solve.IP.IntegerPb where

import Control.Monad
import Control.Monad.Cont
import Control.Monad.State
import Data.List
import qualified Data.Map as M
import Data.Array

import Solve.IP.BranchBound
import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.Dual
import Solve.Simplex.StandardSimplex


data IntegerPb = IntegerPb {getRelax :: LinearPb,
                            getInteger :: [DVar],
                            floatIntegerVar :: [(DVar,Coefficient)]}
          deriving Show


type IntegerPbS = State IntegerPb

emptyIp = IntegerPb emptyPb [] []

{- Exécute une opération sur le problème relaxé (on relache les contraintes d'intégrité)-}
liftIP     :: LinearPbS t -> IntegerPbS t
liftIP act =  do
  ip <- get
  let (ans,lp') = runState act (getRelax ip)
  put $ ip{getRelax = lp'}
  return ans

{- Génère n variables entières -}
ipNewIntegerVars   :: Integer -> IntegerPbS [DVar]
ipNewIntegerVars n =  do
  dvar <- liftIP $ newVars n
  ip <- get
  put $ ip {getInteger = dvar ++ getInteger ip}
  return dvar

{- Le cas trivial est atteint quand toutes les variables entières en base
   respectent les contraintes d'intégrité.
   Résoudre un problème trivial consiste à récupérer la solution optimale d'un tel problème -}
instance OptNode IntegerPb where
  trivial ip = null $ floatIntegerVar ip
  solve ip = - (getZ $ getRelax ip)
  
pBorne :: IntegerPb -> Double
pBorne ip = - (getZ $ getRelax ip)

pEval :: IntegerPb -> Double
pEval _ = - infty

{- On considère la première variable xi qui devrait être entière, mais qui ne l'est pas,
   on construit le problème p1 (resp p2) où on ajoute la contrainte xi <= E(xi) (resp xi >= E(xi) + 1)
-}
pBranch' :: IntegerPbS [IntegerPb]
pBranch' = do
  [ct] <- liftIP $ newCtrs 1
  ip <- get
  let (dvar,val) = head $ floatIntegerVar ip
      -- c1 : {xi <= E(val)}
      -- c2 : {xi >= E(val) + 1} => {- xi <= -1 - E(val)}
      -- NB : Ne considérer que les contraintes réalisables
      ct1 = [(dvar,1)] `LowerOrEqual` (fromIntegral $ truncate val)
      ct2 = [(dvar,-1)] `LowerOrEqual`  ( - 1 - (fromIntegral $ truncate val))
  return $ map snd [ runState ((liftIP $ reoptCtr [ct] ct1) >> buildCurrentLP) ip,
                     runState ((liftIP $ reoptCtr [ct] ct2) >> buildCurrentLP) ip]    
 
pBranch p = fst $ runState pBranch' p

{- On copie le problème actuel, on le résoud par le dual et on extrait
   les variables entières qui ne le sont pas -}
buildCurrentLP :: IntegerPbS ()
buildCurrentLP = do
  
  --liftCurrentIP simplexDual  
  ans <- liftIP simplexDual
  
  -- Si on obtient une solution infinie (polyèdre non borné, on arrête immédiatement la recherche
  -- (on dit que toutes les variables sont entières et on fixe la oslution du pb à -infty)
  z <- liftIP $ gets getZ
        
  sol <- liftIP extraireSolution
  ip <- get
  if ans == Infinite
  then put $ ip{getRelax = (getRelax ip){getZ = infty},
                floatIntegerVar = []}
  else put $ ip{floatIntegerVar = [(val, coeff) | (val, coeff) <- sol,
       			                                      val `elem` (getInteger ip),
       			                                      coeff /= fromIntegral (truncate coeff)]}
  return ()


data KnapSack = KnapSack {gains :: [Double],
                          couts :: [Double],
                          capacite :: Double}
knapsack :: KnapSack -> IntegerPbS ()
knapsack k = do
 let nbVars = fromIntegral $ length $ gains k
 dvars <- ipNewIntegerVars nbVars
 liftIP $ setObj Minimize $ zip dvars (gains k)
 [ct] <- liftIP $ newCtrs 1
 liftIP $ forceCtr [ct] $ (zip dvars (map (*(-1)) (couts k))) `LowerOrEqual` (- capacite k)
 
 liftIP please 
 return ()
 
k1 = KnapSack [10,8,5] [6,5,4] 9


ip1 = snd $ runState (knapsack k1) emptyIp

{- Optimise le problème en nombres entiers actuel -}
solveIP :: IntegerPbS Double
solveIP = do
     ip <- get
     let ip' = snd $ runState buildCurrentLP ip
     (pb, opt) <- runCont (branchbound pBranch pBorne pEval ip' (ip',-infty) Max) return
     put pb
     return opt
     
solveKS k = runState (knapsack k >> solveIP) emptyIp
