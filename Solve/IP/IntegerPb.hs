module Solve.IP.IntegerPb where

import Control.Monad
import Control.Monad.State
import Data.List

import Model.Model
import Solve.IP.BranchBound
import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.Dual

data IntegerPb = IntegerPb {getRelax :: LinearPb,
                            getLinear :: [DVar],
                            getInteger :: [DVar],
                            getFixedInteger :: [DVar],
                            floatIntegerVar :: [(DVar,Coefficient)],
                            currentLP :: LinearPb}
          deriving Show


type IntegerPbS = State IntegerPb

emptyIp = IntegerPb emptyPb [] [] [] [] emptyPb

{- Exécute une opération sur le problème relaxé (on relache les contraintes d'intégrité)-}
liftIP     :: LinearPbS t -> IntegerPbS t
liftIP act =  do
  ip <- get
  let (ans,lp') = runState act (getRelax ip)
  put $ ip{getRelax = lp'}
  return ans
  
liftCurrentIP :: LinearPbS t -> IntegerPbS t
liftCurrentIP act =  do
  ip <- get
  let (ans,lp') = runState act (currentLP ip)
  put $ ip{currentLP = lp'}
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
  

{- Le cas trivial est atteint quand toutes les variables entières en base
   respectent les contraintes d'intégrité.
   Résoudre un problème trivial consiste à récupérer la solution optimale d'un tel problème -}
instance OptNode IntegerPb where
  trivial ip = null $ floatIntegerVar ip
  solve ip = getZ $ currentLP ip
  
pEval :: IntegerPb -> Double
pEval ip = getZ $ currentLP ip

pBorne :: IntegerPb -> Double
pBorne _ = infty

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
      ct1 = [(dvar,1)] `LowerOrEqual` (fromIntegral $ truncate val)
      ct2 = [(dvar,-1)] `LowerOrEqual` ( -1 - (fromIntegral $ truncate val))
  return $ map snd [ runState ((liftIP $ forceCtr ct ct1) >> buildCurrentLP) ip,
                     runState ((liftIP $ forceCtr ct ct2) >> buildCurrentLP) ip]    
 
{- On copie le problème actuelle, on le résoud par le dual et on extrait
   les variables entières qui ne le sont pas -}
buildCurrentLP :: IntegerPbS ()
buildCurrentLP = do
  ip <- get
  put $ ip{currentLP = getRelax ip}
  liftCurrentIP simplexDual
  
  sol <- liftCurrentIP extraireSolution
  ip <- get
  
  put $ ip{floatIntegerVar = [(val, coeff) | (val,coeff) <- sol,
                                             val `elem` (getInteger ip)]}
  return ()

