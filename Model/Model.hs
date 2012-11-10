module Model.Model where
import Control.Monad.State
import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.StandardSimplex

import Data.Maybe
import Data.Map hiding (foldl)
data Model = Model {getLP :: LinearPb,
                    getLinearDVar :: Map DVar String,
                    getIntegerDVar :: Map DVar String}
             deriving Show
data SimplexAns = SimplexAns {solType :: OptAns,
                              finalLP :: LinearPb,
                              solutions :: Map String Double}
             deriving Show
type ModelS = State Model

emptyModel = Model emptyPb empty empty

setLinName :: DVar -> String -> ModelS ()
setLinName xi label = do
  m <- get
  put $ m{getLinearDVar = insert xi label (getLinearDVar m)}

solve :: ModelS SimplexAns
solve = do
  model <- get
  lp <- gets getLP
  let (ans,final) = runState simplex lp
      (base,_) = runState extraireSolution lp
      sols = foldl (\a (xi,v) -> let lname = xi `Data.Map.lookup` getLinearDVar model
                                     iname = xi `Data.Map.lookup` getIntegerDVar model
                                 in if isJust lname then (fromJust lname,v):a
                                    else if isJust iname then (fromJust iname,v):a
                                    else (show xi,v):a) [] base
  return $ SimplexAns ans final (fromList sols)
  
  
liftModel :: LinearPbS t -> ModelS t
liftModel act = do
  model <- get
  let (ans, lp') = runState act (getLP model)
  put $ model{getLP = lp'}
  return ans