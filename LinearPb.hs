module LinearPb where

import Data.Array
import Data.List
import Control.Monad.State
import Debug.Trace
type Array2D = Array (Integer,Integer)
type Array1D = Array Integer

type DVar = Integer
type Ctr = Integer
type Coefficient = Double

data OptAns = Opt | Infinite | Err
          deriving Show

data LinearPb = LinearPb { getA :: Array2D Double,
                           getB :: Array1D Double,
                           getC :: Array1D Double}
              deriving Show

type LinearPbS = State LinearPb           


{- Fonction ajoutant k nouvelles variables au problème et
 allouant la mémoire aux tableaux nécessaires 
             -> ajout de k colonnes à A
             -> ajout de k cases à C
 Retourne l'indice de la variable pour des manipulations exterieures-}
newVars :: Integer -> LinearPbS [DVar]
newVars k = do
  p <- get
  let a = getA p
      (binf,(nbCtr,nbVar)) = bounds a
  put $ p{getA = array (binf,(nbCtr,nbVar + k)) (assocs a ++ [((i,nbVar +j),0) | j <- [1..k], i <- [fst binf.. nbCtr]]),
          getC = array (snd binf, nbVar +k) ([(nbVar+i,0) | i <- [1..k]] ++ (assocs $ getC p))}
  return $ [nbVar + i | i <- [1..k]]
  
{- Fonction ajoutant une nouvelle contrainte au problème :
            -> Ajout d'une ligne à A
            -> Ajout d'une case à B -}
newCtrs :: Integer -> LinearPbS [Ctr]
newCtrs k = do
  p <- get
  let a = getA p
      (binf,(nbCtr,nbVar)) = bounds a
  put $ p{getA = array (binf,(nbCtr+k, nbVar)) (assocs a ++ [((nbCtr+j,i),0) | j<- [1..k], i <- [snd binf.. nbVar]]),
          getB = array (fst binf, nbCtr + k) ([(nbCtr + j,0) | j <- [1..k]]++assocs (getB p))}
  return $ [nbCtr + j | j <- [1..k]]
  
{- Fonction modifiant la contrainte avec les coefficients spécifiés -}
setCtr :: Ctr -> [(DVar,Coefficient)] -> Coefficient -> LinearPbS ()
setCtr ind tuples bi = do
  p <- get
  put $ p{getA = getA p // map (\ (dvar,ci) -> ((ind,dvar),ci)) tuples,
          getB = getB p // [(ind,bi)]}
    
-- Positionne un coefficient sur la fonction objectif
setCi :: DVar -> Coefficient -> LinearPbS ()    
setCi xi ci = do
  p <- get
  put $ p{getC = getC p // [(xi,ci)]}
emptyPb = LinearPb (array ((0,0),(0,0)) [((0,0),0)]) (array (0,0) [(0,0)]) (array (0,0) [(0,0)])


-- Calcul du dual d'un problème : on passe de Max sc <= à Min sc >= ou réciproquement
dual :: LinearPbS ()
dual = do
  p <- get
  let ((m0,n0), (m1,n1)) = bounds $ getA p
  put $ p{getA = array ((n0,m0), (n1,m1)) [((i,j),val) | i <- [n0..n1], j <- [m0..m1], let val = getA p ! (j,i)],
          getB = getC p,
          getC = getB p} 


      
