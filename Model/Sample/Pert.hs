module Model.Sample.Pert where

import Control.Monad
import Control.Monad.State
import Data.Array
import Data.Maybe
import qualified Data.Map as M

import Model.Model
import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.Dual

type IndiceSommet = Integer
type Arc = (IndiceSommet, IndiceSommet)
type Valuation = Double

data Sommet = Sommet {indice :: IndiceSommet,
                      successeurs :: [IndiceSommet],
                      predecesseurs :: [IndiceSommet]}
              deriving Show
data Graphe = Graphe {sommets :: Array IndiceSommet Sommet,
                      arcs :: M.Map Arc Valuation}
              deriving Show

type GrapheS = State Graphe

emptyGraph n0 n1  = Graphe (array (n0,n1) [(i,Sommet i [] []) | i <- [n0..n1]]) (M.empty)

-- ajoute un arc au graphe (modifie les predecesseurs et les successeurs)
ajouterArc :: IndiceSommet -> IndiceSommet -> Valuation -> GrapheS ()
ajouterArc si sj dij = do
  gr <- get
  let sommeti = sommets gr ! si
      sommetj = sommets gr ! sj
  put gr{sommets = sommets gr // [(si, sommeti{successeurs = sj:successeurs sommeti}),
                                  (sj, sommetj{predecesseurs = si:predecesseurs sommetj})],
         arcs = (M.insert (si,sj) dij $ arcs gr)}
  

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
  (tmax:dvar) <- liftModel $ newVars (sn - s1+2)
  
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
  liftModel $ setObj Minimize [(tmax,1)]
  -- On alloue suffisament de contraintes et on les applique
  ctrs <- liftModel $ newCtrs $ fromIntegral $ length ctrTot
  liftModel $ foldM (\_ (ci,ctr) -> forceCtr ci ctr) [] $ zip ctrs ctrTot
  
  -- On nomme les variables par commodité
  setLinName tmax "Tmax"
  foldM (\_ (si,ti) -> setLinName ti $ "S" ++ show si ) () (assocs sTab)
  liftModel please
  
  -- On résoud le problème par l'algorithme dual
  ans <- liftModel simplexDual
  m <- get
  base <- liftModel extraireSolution
  
  -- On extrait les solutions de base
  return (ans, [(fromJust nom,val) | (xi,val) <- base, let nom = xi `M.lookup` getLinearDVar m, isJust nom])
  
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
