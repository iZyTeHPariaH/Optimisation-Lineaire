module Solve.IP.IntegerPb where

import Control.Monad
import Control.Monad.State
import Data.List

import Model.Model
import Solve.IP.BranchBound
import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.StandardSimplex

data IntegerPb = IntegerPb {getRelax :: LinearPb,
                            getLinear :: [DVar],
                            getInteger :: [DVar],
                            getFixedInteger :: [DVar],
                            currentLP :: LinearPb}
          deriving Show


type IntegerPbS = State IntegerPb

emptyIp = IntegerPb emptyPb [] [] [] emptyPb

{- Exécute une opération sur le problème relaxé (on relache les contraintes d'intégrité)-}
liftIP     :: LinearPbS t -> IntegerPbS t
liftIP act =  do
  ip <- get
  let (ans,lp') = runState act (getRelax ip)
  put $ ip{getRelax = lp'}
  return ans
  

{- Génère n variables linéaires -}
ipNewLinearVars   :: Integer -> IntegerPbS [DVar]
ipNewLinearVars n =  do
  dvar <- liftIP $ newVars n
  ip <- get
  put $ ip{getLinear = dvar ++ getLinear ip}
  return dvar

{- Génère n variables entières -}
ipNewIntegerVars   :: Integer -> IntegerPbS [DVar]
ipNewIntegerVars n =  do
  dvar <- liftIP $ newVars n
  ip <- get
  put $ ip {getInteger = dvar ++ getInteger ip}
  return dvar

ipSetIntegerVar :: DVar -> Integer -> IntegerPbS ()
ipSetIntegerVar xi k = do
  [ci] <- liftIP $ newCtrs 1
  liftIP $ forceCtr ci $ [(xi,1)] `Equal` (fromIntegral k)
  ip <- get
  put $ ip{getInteger = getInteger ip \\ [xi],
           getFixedInteger = xi : getFixedInteger ip}
  

{- Le cas trivial est atteint quand il n'y a plus de variables à fixer, ou quand toutes les 
   variables 0-1 en base respectent les contraintes d'intégrité.
   Résoudre un problème consiste à récupérer la valeur de l'optimum actuel.-}
instance OptNode IntegerPb where
  trivial ip = (null $ getInteger ip) || (and x)
      where (base,_) = runState extraireSolution (currentLP ip)
            x = map (\(_,t) -> t == fromIntegral (truncate t)) 
                    [(xi,vi) | (xi,vi) <- base, xi `elem` getInteger ip]
  solve ip = getZ $ currentLP ip
  
pBorne :: IntegerPb -> Double
pBorne ip = getZ $ currentLP ip

--pEval :: IntegerPb -> Double


