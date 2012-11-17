module Solve.LP.LPBuild where

import Solve.LP.LinearPb
import Control.Monad
import Control.Monad.State
import GHC.Float
import Data.Array
import qualified Data.Map as M
import Data.Maybe
import Debug.Trace
type CoeffList = [(DVar,Coefficient)]

data OptCrit = Maximize | Minimize
data Constraint = CoeffList `LowerOrEqual` Double |
                  CoeffList `Equal` Double        |
                  CoeffList `GreaterOrEqual` Double 
                  
ctTuple (c1 `LowerOrEqual` b) = (c1,b)
ctTuple (c1 `Equal` b) = (c1,b)
ctTuple (c1 `GreaterOrEqual` b) = (c1,b)

ctConst (LowerOrEqual _ _) = LowerOrEqual
ctConst (Equal _ _) = Equal
ctConst (GreaterOrEqual _ _) = GreaterOrEqual

remplacerNoms clist m = [(fromJust li,vi) |(xi,vi) <-clist, let li = xi `M.lookup` m, isJust li ]
show' m (c `LowerOrEqual` b) = let noms = remplacerNoms c m 
                                   affCouple(nom,coeff) = if coeff > 0 then " + "++show coeff++ nom
                                                          else if coeff < 0 then show coeff ++ nom 
                                                          else ""                                   
                               in concat (map affCouple noms) ++ "<=" ++ show b++";\n"
show' m (c `Equal` b) = let noms = remplacerNoms c m 
                            affCouple(nom,coeff) = if coeff > 0 then " + "++show coeff++ nom
                                                   else if coeff < 0 then show coeff ++ nom
                                                   else ""                                   
                               in concat (map affCouple noms) ++ "=" ++ show b++";\n"
show' m (c `GreaterOrEqual` b) = let noms = remplacerNoms c m 
                                     affCouple(nom,coeff) = if coeff > 0 then " + "++show coeff++ nom
                                                            else if coeff < 0 then  show coeff ++ nom
                                                            else ""                                   
                               in concat (map affCouple noms) ++ ">=" ++ show b++";\n"

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
        addBase xi ci
        setCtr ci ((xi,1):clist) bi
        return $ Just xi
      else do
        [xi,yi] <- newVars 2
        addEcart xi
        addArt yi
        addBase yi ci
        setCtr ci ((yi,1):(xi,-1):map (\(xk,ak) -> (xk, -ak) ) clist) (-bi)
        return $ Just xi    
        
    GreaterOrEqual clist bi -> if bi <= 0 
      then do
        [xi] <- newVars 1
        addEcart xi
        addBase xi ci
        setCtr ci ((xi,1):(map (\(xi,ai) -> (xi, -ai)) clist)) (- bi)
        return $ Just xi
      else do
        [xi,yi] <- newVars 2
        addEcart xi
        addArt yi
        addBase yi ci
        setCtr ci ((xi,-1):(yi,1):clist) bi
        return $ Just xi
    Equal clist bi -> do
      [yi] <- newVars 1
      addArt yi
      addBase yi ci
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
  addBase e ci 
  return [e]

forceCtr [ci,ci'] (clist `Equal` bi) = do
  [e1,e2] <- newVars 2  
  setCtr ci ((e1,1):clist) bi
  setCtr ci' ((e1,1):(map (\(xi,vi) -> (xi, -vi)) clist )) (- bi)
  addBase e1 ci 
  addBase e2 ci' 
  return [e1,e2]

forceCtr [ci] (clist `GreaterOrEqual` bi) = do
  [e] <- newVars 1
  forceCtr [ci] $ (map (\ (xi,val) -> (xi,-val)) clist) `LowerOrEqual` (-bi)
  

{- Retourne la liste des coefficients contenus à la ligne spécifiée -}
getCtr :: Array2D Double -> Ctr -> [Coefficient]
getCtr a ci = let ((_,n0),(_,n1)) = bounds $ a
              in [a ! (ci,j) | j <- [n0..n1] ]
  
{- Modifie la contrainte spécifiée (avec la variable d'écart indiqué)
 en la changeant de base si necessaire -}
reoptCtr' :: DVar -> Ctr ->  LinearPbS ()
reoptCtr' ec indice = do
  p <- get
  let a = getA p 
      b = getB p
      base = getBase p
      ((m0,n0),(m1,n1)) = bounds a
      ligne = zip [n0..] $ getCtr a indice
      sndMembre = b ! indice
      
      {- Pour chaque variable de base xj (associée à ci) présente dans la contrainte l,
         on effectue le calcul l <- l - ci*coeff
                               bl <- bl - bi * coeff -}
      (ligne',bi',k) = foldl (\(l,bi,i) (xj,coeff) -> if i == m1 - m0 + 1 then (l,bi,i)
                                                      else
                                                      case xj `M.lookup` base of
                                                        Nothing -> (l,bi,i)
                                                        Just ci -> ( zipWith (\(coord,val) val' -> (coord,val - coeff*val') ) l (getCtr a ci),
                                                                     bi - coeff* (b ! ci),
                                                                     i+1)   )  
                       (ligne,sndMembre,0) 
                       ligne
                       
  put $ p{getB = b // [(indice,bi')],
          getA = a // ([((indice,xi),v) |(xi,v) <-ligne'])}
  
-- Réoptimise une fonction objectif  
-- Attention, il faut qu'elle concerne tous les coefficients
reoptObj dir c = do
  p <- get
  let a = getA p
      b = getB p
      opt = getZ p
      base = getBase p
      ((m0,_), (m1,_)) = bounds a
      (c',z',_) = foldl (\(couts,z, i) (xi,coeffi) -> if i == m1 - m0 + 1 then (couts,z,i) 
                                                      else case xi `M.lookup` base of
                                                        Nothing -> (couts,z,i)
                                                        Just ci -> (zipWith (\(coord,val) val' -> (coord, val - coeffi*val')) 
                                                                    couts 
                                                                    (getCtr a ci) , 
                                                                    z - coeffi*(b ! ci),
                                                                    i+1) )
                  (c,0,0) 
                  c
  setObj dir c'
  p' <- get
  put p'{getZ = z'}
  return ()

{- Réoptimise sans normaliser -}
reoptCtr :: [Ctr] -> Constraint -> LinearPbS ()
reoptCtr cilist ctr = do
  ec <- forceCtr cilist ctr
  -- On sort les variables de la base (le temps qu'on normalise la contrainte)
  foldM (\_ ci -> outBase ci) () cilist
  foldM (\ _ (e,ct) -> reoptCtr' e ct) () $ zip ec cilist
  -- On les rajoute
  foldM (\_ (xi,ci) -> addBase xi ci) () $ zip ec cilist
  return ()    

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
extraireSolution :: LinearPbS [(DVar,Coefficient)]
extraireSolution = do
  p <- get
  return [(xi,getB p ! ci) | (xi,ci) <- M.toList (getBase p)]



      
