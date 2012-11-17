module Solve.LP.LinearPb where

import Data.Array
import Data.Maybe
import qualified Data.Map as M
import Data.List
import Control.Monad.State
import Debug.Trace
type Array2D = Array (Integer,Integer)
type Array1D = Array Integer

type DVar = Integer
type Ctr = Integer
type Coefficient = Double

infty = let (mm,mM) = floatRange (0::Double)
        in ((2^(mM-1))::Double) + 1

data OptAns = Opt | Infinite | NotReal
          deriving (Show, Eq)

data LinearPb = LinearPb { getA :: Array2D Double,
                           getB :: Array1D Double,
                           getC :: Array1D Double,
                           getZ :: Double,
                           getEcart :: [DVar],
                           getArt :: [DVar],
                           getBase :: M.Map DVar Ctr,
                           getBaseDuale :: M.Map Ctr DVar}
addEcart xi = do
  p <- get
  put $ p{getEcart = xi:getEcart p}
  
addArt ai = do
  p <- get
  
  put $ p{getArt = ai: getArt p{-,
          getC = getC p // [(ai,-infty)],
          getZ = infty-}}
addBase xi ci = do
  p <- get
  put $ p{getBase = M.insert xi ci (getBase p),
          getBaseDuale = M.insert ci xi (getBaseDuale p)}
outBase ci = do
  p <- get
  let base = getBase p
      baseDuale = getBaseDuale p
      xi = ci `M.lookup` baseDuale
  if isJust xi
  then  put $ p{getBase = M.delete (fromJust xi) base,
                getBaseDuale = M.delete ci baseDuale}
  else return ()


--fonction qui a une liste de couple (indice,valeur) associe "valeur*x indice"
affLigne l = let affElem (a,b) = if b>0 then " + "++(show b)++" x"++(show a)
                                 else if b<0 then " - "++drop 1 (show b)++" x"++(show a)
                                 else ""
         	   in (concat (map affElem l))

affContraintes :: Array2D Double -> Array1D Double -> String      
affContraintes a b = let ((m0,n0), (m1,n1)) = bounds a
                         ligne i = [(k,a ! (i,k)) | k <- [n0..n1]]
                         tuples = zip [ligne i | i <- [m0..m1]] [b ! i | i <- [m0..m1]]
                         affLi (c,b') = affLigne c ++" = "++ show b' ++"\n"
                     in concat (map affLi tuples)

instance Show LinearPb where
 show p = "/* Fction Obj */\nmax : "++ affLigne (assocs (getC p)) ++ "=" ++ show (getZ p) ++
          "\n"++"\n/* Sous Contraintes */\n\n"++ affContraintes (getA p) (getB p)
          
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

emptyPb = LinearPb (array ((0,0),(0,0)) [((0,0),0)]) (array (0,0) [(0,0)]) (array (0,0) [(0,0)]) 0 [] [] M.empty M.empty



