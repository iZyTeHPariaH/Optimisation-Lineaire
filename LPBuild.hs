module LPBuild where

import LinearPb
import Control.Monad
import Control.Monad.State
import GHC.Float
import Data.Array

type CoeffList = [(DVar,Coefficient)]

data OptCrit = Maximize | Minimize
data Constraint = CoeffList `LowerOrEqual` Double |
                  CoeffList `Equal` Double        |
                  CoeffList `GreaterOrEqual` Double 


{- Positionne les coefficients de la fonction objectif
  (on prend l'opposé s'il s'agit de la minimiser) -}
setObj             :: OptCrit -> CoeffList -> LinearPbS ()
setObj crit tuples =  foldM (\_ (xi,ci) -> setCi xi ci) () tuples'
    where tuples' = case crit of
            Maximize -> tuples
            Minimize -> map (\ (xi,ci) -> (xi, -ci)) tuples

{- Ajoute la contrainte spécifiée au problème.
 S'il est nécessaire d'introduire une variable d'écart, la fonction retourne
 son indice. -}
addConstraint   :: Ctr -> Constraint -> LinearPbS (Maybe DVar)
addConstraint ci c =   case c of
    LowerOrEqual clist bi -> do 
      [xi] <- newVars 1
      setCtr ci ((xi,1):clist) bi
      return $ Just xi
    GreaterOrEqual clist bi -> do
      [xi] <- newVars 1
      setCtr ci ((xi,1):(map (\(xi,ai) -> (xi, -ai)) clist)) (- bi)
      return $ Just xi
    Equal clist bi -> do
      setCtr ci clist bi
      return $ Nothing
  
please :: LinearPbS ()  
please = do
  p <- get
  let a = getA p
      ((m0,n0),(m1,n1)) = bounds a
  put $ p{getA = array ((m0+1,n0+1), (m1,n1)) [(coord,val) | (coord@(i,j),val) <- assocs $ a,
                                                             i > 0, j > 0],
          getB = array (m0+1,m1) (tail $ assocs $ getB p),
          getC = array (n0+1, n1) (tail $ assocs $ getC p)}