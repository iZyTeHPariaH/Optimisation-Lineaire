module Solve.LP.LPBuild where

import Solve.LP.LinearPb
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
    LowerOrEqual clist bi -> if bi >= 0
      then do
        [xi] <- newVars 1
        addEcart xi
        setCtr ci ((xi,1):clist) bi
        return $ Just xi
      else do
        [xi,yi] <- newVars 2
        addEcart xi
        addArt yi
        setCtr ci ((yi,1):(xi,-1):map (\(xk,ak) -> (xk, -ak) ) clist) (-bi)
        return $ Just xi    
        
    GreaterOrEqual clist bi -> if bi <= 0 
      then do
        [xi] <- newVars 1
        addEcart xi
        setCtr ci ((xi,1):(map (\(xi,ai) -> (xi, -ai)) clist)) (- bi)
        return $ Just xi
      else do
        [xi,yi] <- newVars 2
        addEcart xi
        addArt yi
        setCtr ci ((xi,-1):(yi,1):clist) bi
        return $ Just xi
    Equal clist bi -> do
      [yi] <- newVars 1
      addArt yi
      setCtr ci ((yi,1):clist) bi
      return $ Nothing
  
addConstraintList :: [(Ctr, Constraint)] -> LinearPbS [(Ctr,Maybe DVar)]
addConstraintList clist = foldM (\a (ci,ct) -> addConstraint ci ct >>= \v -> return ((ci,v):a)) [] clist

please :: LinearPbS ()  
please = do
  p <- get
  let a = getA p
      ((m0,n0),(m1,n1)) = bounds a
  put $ p{getA = array ((m0+1,n0+1), (m1,n1)) [(coord,val) | (coord@(i,j),val) <- assocs $ a,
                                                             i > 0, j > 0],
          getB = array (m0+1,m1) (tail $ assocs $ getB p),
          getC = array (n0+1, n1) (tail $ assocs $ getC p),
          getZ = 0}
    
extraireSolution :: LinearPbS CoeffList
extraireSolution = do
  p <- get
  let a = getA p
      ((m0,n0),(m1,n1)) = bounds a
      base = [(xi,val) | xi <- [n0..n1],
                         getC p ! xi == 0,
                         let pivs = [(i, a ! (i,xi)) | i <- [m0..m1], a ! (i,xi) /= 0]
                             val = getB p ! (fst $ head pivs),
                         length pivs == 1,
                         1 == (snd $ head pivs)]
  return base
-- Calcul du dual d'un problème : on passe de Max sc <= à Min sc >= ou réciproquement
{-
dual :: LinearPbS ()
dual = do
  p <- get
  let ((m0,n0), (m1,n1)) = bounds $ getA p
  put $ p{getA = array ((n0,m0), (n1,m1)) [((i,j),val) | i <- [n0..n1], j <- [m0..m1], let val = getA p ! (j,i)],
          getB = getC p,
          getC = getB p} -}

dual :: LinearPbS ()
dual = do
  p <- get
  let a = getA p
      ((m0,n0),(m1,n1)) = bounds a
  put $ LinearPb (array ((n0,m0),(n1,m1)) [((i,j),0) | i <- [n0..n1], j <- [m0..m1]])
                 (array (n0,n1) $ zip [n0..n1] $ repeat 0)
                 (array (m0,m1) $ zip [m0..m1] $ repeat 0)
                 0
                 []
                 []
  setObj Minimize (assocs $ getB p)
  foldM (\_ xi -> addConstraint xi $ [(ci,a ! (ci,xi)) | ci <- [m0..m1]] `GreaterOrEqual`   ((getC p) ! xi)) Nothing [n0..n1]
  return ()


      
