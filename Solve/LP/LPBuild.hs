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

{- Normalise puis ajoute la contrainte spécifiée au problème.
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

{- Normalise et ajoute successivement les contraintes d'une liste -}  
addConstraintList :: [(Ctr, Constraint)] -> LinearPbS [(Ctr,Maybe DVar)]
addConstraintList clist = foldM (\a (ci,ct) -> addConstraint ci ct >>= \v -> return ((ci,v):a)) [] clist

{- Ajoute une contrainte sans la normaliser (utile pour appliquer l'algorithme dual)-}
forceCtr :: [Ctr] -> Constraint -> LinearPbS [DVar] 
forceCtr [ci] (clist `LowerOrEqual` bi) = do 
  [e] <- newVars 1
  setCtr ci ((e,1):clist) bi
  return [e]

forceCtr [ci,ci'] (clist `Equal` bi) = do
  [e1,e2] <- newVars 2  
  setCtr ci ((e1,1):clist) bi
  setCtr ci' ((e1,1):(map (\(xi,vi) -> (xi, -vi)) clist )) bi
  return [e1,e2]

forceCtr [ci] (clist `GreaterOrEqual` bi) = do
  [e] <- newVars 1
  forceCtr [ci] $ (map (\ (xi,val) -> (xi,-val)) clist) `LowerOrEqual` (-bi)
{- Nettoie le problème en supprimant les artefacts créés à partir du problème vide.
 ATTENTION : Il est impératif d'utiliser la fonction une et une seule fois lors de la création
             d'un problème.-}
please :: LinearPbS ()  
please = do
  p <- get
  let a = getA p
      ((m0,n0),(m1,n1)) = bounds a
  put $ p{getA = array ((m0+1,n0+1), (m1,n1)) [(coord,val) | (coord@(i,j),val) <- assocs $ a,
                                                             i > 0, j > 0],
          getB = array (m0+1,m1) (tail $ assocs $ getB p),
          getC = array (n0+1, n1) (tail $ assocs $ getC p)}

{- Extrait la base actuelle du problème. -}    
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



      
