import LinearPb
import LPBuild
import StandardSimplex

import Control.Monad.State
import Data.Array

probleme1 =  do
  [x1,x2] <- newVars 2
  [c1,c2,c3] <- newCtrs 3
  setObj Maximize [(x1,1),(x2,1)]
  addConstraint c1 $ [(x1,2),(x2,1)] `LowerOrEqual` 14
  addConstraint c2 $ [(x1,-1),(x2,2)] `LowerOrEqual` 8
  addConstraint c3 $ [(x1,2),(x2,-1)] `LowerOrEqual` 10
  please
  return ()
