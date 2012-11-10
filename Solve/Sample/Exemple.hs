module Solve.Sample.Exemple where

import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.StandardSimplex

import Control.Monad.State
import Data.Array

{- Max x1 + 2x2
 sc 2x1 + x2 <= 14
    -x1 + 2x2 <= 8
    2x1 - x2 <= 10 -}

p1 =  do
  [x1,x2] <- newVars 2
  [c1,c2,c3] <- newCtrs 3
  setObj Maximize [(x1,1),(x2,1)]
  addConstraint c1 $ [(x1,2),(x2,1)] `LowerOrEqual` 14
  addConstraint c2 $ [(x1,-1),(x2,2)] `LowerOrEqual` 8
  addConstraint c3 $ [(x1,2),(x2,-1)] `LowerOrEqual` 10
  please
  return ()

{- Max -7x1 + 3x2
 sc -x1 - x2 <= -2
    x1 + 2x2 <= 2
    8x1 + x2 <= 8 -}  
p2 = do
  [x1,x2] <- newVars 2
  [c1,c2,c3] <- newCtrs 3
  setObj Maximize [(x1,-7),(x2,3)]
  addConstraint c1 $ [(x1,-1),(x2,-1)] `LowerOrEqual` (-2)   
  addConstraint c2 $ [(x1,1), (x2,2)] `LowerOrEqual` 2
  addConstraint c3 $ [(x1,8),(x2,1)]  `LowerOrEqual` 8
  please
  

{- Max 5x1 + 6x2
 sc -x1 + x2 <= 4
    5x1 + 3x2 <= 60
    x2 >= 5 -}  
p3 = do  
  [x1,x2,a1] <- newVars 3
  [c1,c2,c3] <- newCtrs 3
  setObj Maximize [(x1,5), (x2,6)]
  addConstraint c1 $ [(x1,-1),(x2,1)] `LowerOrEqual` 4
  addConstraint c2 $ [(x1,5),(x2,3)] `Equal` 60
  addConstraint c3 $ [(x2,1)] `GreaterOrEqual` 5
  please
