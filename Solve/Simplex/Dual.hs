module Solve.Simplex.Dual where
import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.StandardSimplex

import Control.Monad
import Control.Monad.State
import Data.Array
import Data.List

{- Application de l'algorithme dual du simplexe à partir
 d'une base optimale non réalisable. -}
simplexDual :: LinearPbS OptAns
simplexDual = do
  p <- get
  let a = getA p
      ((m0,n0),(m1,n1)) = bounds a
      candidatsSortants = [(xi,bi) | xi <- [m0..m1], let bi = getB p ! xi, bi < 0]
      (ipiv,meilleurBi) = head $ sortBy (\(x1,b1) (x2,b2) -> compare b1 b2) candidatsSortants
      candidatsEntrants = [(xi,piv,ri) | xi <- [n0..n1], let piv = a ! (ipiv,xi) 
                                                             ri = (getC p ! xi) / piv ,
                                         piv < 0]
      (jpiv, piv, ratio) = head $ sortBy ( \(xi,pi,ri) (xj,pj,rj) -> compare ri rj) candidatsEntrants
  if null candidatsSortants
     then return Opt
  else if null candidatsEntrants
     then return Infinite
  else do echelonner (ipiv,jpiv) piv
          simplexDual
  
