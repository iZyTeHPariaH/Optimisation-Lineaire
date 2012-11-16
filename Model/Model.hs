module Model.Model where
import Control.Monad.State

import Solve.IP.IntegerPb
import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.StandardSimplex

import Data.Maybe
import Data.Map hiding (foldl)
data Model = Model {getIP :: IntegerPb,
                    getDVarMap :: Map DVar String}
             deriving Show
data SimplexAns = SimplexAns {solType :: OptAns,
                              finalLP :: LinearPb,
                              solutions :: Map String Double}
             deriving Show
type ModelS = State Model

emptyModel = Model emptyIp empty

{- Affecte une étiquette à une variable de décision -}
setDVarName :: DVar -> String -> ModelS ()
setDVarName xi label = do
  m <- get
  put $ m{getDVarMap = insert xi label (getDVarMap m)}

{- Applique une transformation sur le problème du modèle -}  
liftModel :: IntegerPbS t -> ModelS t
liftModel act = do
  model <- get
  let (ans, ip') = runState act (getIP model)
  put $ model{getIP = ip'}
  return ans

liftModelLP  = liftModel . liftIP

{- Récupère la liste des couples nom - valeur des variables en base -}
mGetSol :: ModelS [(String,Coefficient)]
mGetSol = do
  m <- get
  let lp = getRelax $ getIP m
      (base,_) = runState extraireSolution lp
      ans = [(fromJust name, val) | (xi,val) <- base, let name = xi `Data.Map.lookup` (getDVarMap m), isJust name]
  return ans
  
solveModel :: ModelS ([(String,Coefficient)],Double)
solveModel = do
  ip <- gets getIP
  opt <- liftModel solveIP 
  sol <- mGetSol
  return (sol,opt)