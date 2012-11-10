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
  
forceCtr :: Ctr -> Constraint -> LinearPbS [DVar] 
forceCtr ci (clist `LowerOrEqual` bi) = do 
  [e] <- newVars 1
  setCtr ci ((e,1):clist) bi
  return [e]

pertPb    :: Graphe -> ModelS ()
pertPb gr = do
  let somm = sommets gr
      (s1,sn) = bounds somm
      
  (tmax:dvar) <- liftModel $ newVars (sn - s1+2)
  
  let sTab = array (s1,sn) (zip [s1..sn] dvar)
      ctrMax = [[(ti,1), (tmax, -1)] `LowerOrEqual` 0 | ti <- dvar]
      ctrDebut = [ [(ti,1), (tj, -1)] `LowerOrEqual` (- val) |   i <- [s1..sn],
                                                               let si = somm ! i,
                                                               j <- successeurs si,
                                                               let sj = somm ! j
                                                                   val = fromJust $ (i,j) `M.lookup` arcs gr
                                                                   ti = sTab ! i
                                                                   tj = sTab ! j ]
      ctrTot = ctrMax   ++ ctrDebut
  {- Min tmax
     sc  pour toute tache i, les successeurs ne peuvent commencer avant ti + di
         pour toute tache i, ti < tmax -}
  liftModel $ setObj Minimize [(tmax,1)]
  ctrs <- liftModel $ newCtrs $ fromIntegral $ length ctrTot
  liftModel $ foldM (\_ (ci,ctr) -> forceCtr ci ctr) [] $ zip ctrs ctrTot
  
  setLinName tmax "Tmax"
  foldM (\_ (si,ti) -> setLinName ti $ "S" ++ show si ) () (assocs sTab)
  liftModel please
  return ()
  
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
