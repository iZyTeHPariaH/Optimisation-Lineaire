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
  
  {-[c1,c2,c3] <- newCtrs 3
  setCtr c1 [(x1,2),(x2,1),(x3,1)] 14
  setCtr c2 [(x1,-1),(x2,2),(x4,1)] 8
  setCtr c3 [(x1,2),(x2,-1),(x5,1)] 10 
  setCi x1 1
  setCi x2 1-}
  p <- get
  put $  p{getA = array ((1,1),(3,5)) [(coord,val) | (coord@(i,j),val) <- assocs $ getA p,
                                                     i > 0, j > 0],
           getB = array (1,3) (tail $ assocs $ getB p),
           getC = array (1,5) (tail $ assocs $ getC p)} 
  return ()
