module Solve.Simplex.StandardSimplex where

import Solve.LP.LinearPb
import Data.List
import Control.Monad.State
import Data.Array
import qualified Data.Map as M

-- Echelonne à partir d'un point piv, associé aux coordonnées (ipiv, jpiv)
echelonner (ipiv,jpiv) piv = do
  outBase ipiv
  addBase jpiv ipiv
  
  p <- get
  let a = getA p
      b = getB p
      c = getC p
      base = getBase p
      duale = getBaseDuale
  
  put $ p{getA = a // [((i,j),val) | ((i,j),precval) <- assocs a,
                                     let val = if i == ipiv then precval/piv
                                               else if j == jpiv then 0
                                               else precval - (a ! (ipiv,j)) * (a ! (i,jpiv)) / piv],
          getB = b // [(ct,bi) | (ct,precbi) <- assocs b,
                                 let bi = if ct == ipiv then precbi / piv
                                          else precbi - (b ! ipiv)*(a ! (ct, jpiv) / piv)],
          getC = c // [(j,ci) |(j,precci) <- assocs c,
                                let ci = if j == jpiv then 0
                                         else precci - (a ! (ipiv,j))* (c ! jpiv) / piv ],
          getZ = getZ p - (b ! ipiv) * (c ! jpiv) / piv}
    


-- Résouds le problème standard max sc <=
simplex :: LinearPbS OptAns
simplex = do
  p <- get
  let a = getA p
      b = getB p
      c = getC p
      ((m0,n0),(m1,n1)) = bounds a
      
      {- Les pivots potentiels sont les variables dont les couts réduits sont positifs -}
      pivotsPotentiels = [(dvar,ci) | (dvar,ci) <- assocs c, ci > 0]
      
      {- La variable entrante est celle qui maximise le cout réduit -}
      (jpiv,cmax) = head $ sortBy (\(_,c1) (_,c2) -> if c1 > c2 then LT else GT) pivotsPotentiels
      
      {- Les candidats sortants sont les lignes à coefficients positif -}
      candidatsSortants = [((i,jpiv),val) | i <- [m0..m1],
                                            let val = a ! (i,jpiv),
                                            val > 0]
      
      {- On récupère le pivot en triant les ratios ( candidatSortant / bi) par ordre croissant -}
      ((ipiv,piv),ratio) = head $ sortBy (\ (_,c1) (_,c2) -> compare c1 c2) (map (\((i,_),val) -> ((i,val),(b ! i) / val) )candidatsSortants)
  if null pivotsPotentiels    
     then return Opt
  else if null candidatsSortants
     then return Infinite
  else do echelonner (ipiv,jpiv) piv
          simplex
