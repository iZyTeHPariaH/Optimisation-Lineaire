module Model.Sample.Pert where

import Control.Monad
import Control.Monad.State
import Data.Array
import Data.Maybe
import qualified Data.Map as M

import Model.Model
import Model.Sample.Graph

import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.IP.IntegerPb
import Solve.Simplex.Dual
import Solve.Simplex.StandardSimplex


  

{- Convertit un graphe en un modèle : 
         Min tmax
     sc  pour toute tache i, les successeurs ne peuvent commencer avant ti + di
         pour toute tache i, ti < tmax -}
pertPb    :: Graphe -> ModelS (OptAns, [(String,Double)])
pertPb gr = do
  -- On récupère les sommets et leur intervalle de valeurs
  let somm = sommets gr
      (s1,sn) = bounds somm
  -- On alloue autant de variables de décision que de sommets + 1 (pour modéliser le maximum des dates de début)    
  (tmax:dvar) <- liftModel $ liftIP $ newVars (sn - s1+2)
  
  let -- On crée un tableau associant à chaque sommet sa variable de décision
      sTab = array (s1,sn) (zip [s1..sn] dvar)
      
      -- On ajoute la contrainte du maximum (la date tmax >= ti pour tout sommet i)
      ctrMax = [[(ti,1), (tmax, -1)] `LowerOrEqual` 0 | ti <- dvar]
      
      -- Pour chaque sommet i, la date de début de chaque successeurs j ne peut être inferieure à ti + di
      --   V i, Vj in successeurs i, ti - tj <= -dj
      ctrDebut = [ [(ti,1), (tj, -1)] `LowerOrEqual` (- val) |   i <- [s1..sn],
                                                               let si = somm ! i,
                                                               j <- successeurs si,
                                                               let sj = somm ! j
                                                                   val = fromJust $ (i,j) `M.lookup` arcs gr
                                                                   ti = sTab ! i
                                                                   tj = sTab ! j ]
      ctrTot = ctrMax   ++ ctrDebut
  -- On minimise la plus grande date de début (car c'est celle de la tâche FIN)
  liftModel $ liftIP $ setObj Minimize [(tmax,1)]
  -- On alloue suffisament de contraintes et on les applique
  ctrs <- liftModel $ liftIP $ newCtrs $ fromIntegral $ length ctrTot
  liftModel $ liftIP $ foldM (\_ (ci,ctr) -> forceCtr [ci] ctr) [] $ zip ctrs ctrTot
  
  -- On nomme les variables par commodité
  setDVarName tmax "Tmax"
  foldM (\_ (si,ti) -> setDVarName ti $ "S" ++ show si ) () (assocs sTab)
  liftModel $ liftIP $ please
  
  -- On résoud le problème par l'algorithme dual
  ans <- liftModel $ liftIP $ simplexDual
  m <- get
  sol <- mGetSol
  return (ans, sol)
  
  -- On extrait les solutions de base
  
  
buildG1 = do
  ajouterArc 0 1 0
  ajouterArc 0 2 0
  ajouterArc 0 3 0
  ajouterArc 0 4 0
  
  ajouterArc 1 10 6
  ajouterArc 2 5 1
  ajouterArc 2 6 1
  ajouterArc 3 7 1
  ajouterArc 4 8 2
  
  ajouterArc 5 9 3
  ajouterArc 6 10 5
  ajouterArc 7 11 6
  ajouterArc 8 11 3
  
  ajouterArc 9 10 2
  ajouterArc 10 11 4
  
g1 = snd $ runState buildG1 $ emptyGraph 0 11


