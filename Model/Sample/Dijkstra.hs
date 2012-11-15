module Model.Sample.Dijkstra where


import Control.Monad
import Control.Monad.State
import Data.Array
import Data.Maybe
import qualified Data.Map as M

import Model.Model
import Model.Sample.Pert
import Model.Sample.Graph

import Solve.LP.LinearPb
import Solve.LP.LPBuild
import Solve.Simplex.Dual
import Solve.Simplex.StandardSimplex


{- Résolution du problème du plus court chemin.
  -> On affecte une variable de décision par arc (qui vaudra 1 si l'arc est choisi)
  -> Les contraintes sont : (*) la somme des e1j pour tout prédécesseurs du sommet 1 est plus grande que 1
                            (*) la somme des ejN pour tout successeurs du sommet N est plus grande que 1
                            (*) pour tout sommet j, la somme des arcs arrivant est égale à la somme des arcs 
                                sortants  : somme (eij) = somme (ejk) -}
        

dijkstra :: Graphe -> ModelS ()
dijkstra gr = do
   let somm = sommets gr
       (s1,sn) = bounds somm
       arcS = arcs gr
   
   --  On alloue une variable par arc
   dvar <- liftModelLP $ newVars $ fromIntegral $ M.size arcS
   
   -- On associe chaque arc à sa variable
   let arcsMap = M.fromList $ zip (M.keys arcS) dvar
       -- On doit quitter le sommet s1 une fois
       ct1 = [(e1j, -1) | j <- successeurs $ somm ! s1, let e1j = fromJust $ M.lookup (s1,j) arcsMap] `LowerOrEqual` (- 1)
       
       -- On doit arriver au sommet sn une fois
       ctn = [(ein, -1) | i <- predecesseurs $ somm ! sn, let ein = fromJust $ M.lookup (i,sn) arcsMap] `LowerOrEqual` (- 1)
   
       -- Si on arrive à un sommet, on doit repartir
       cts = [ ([(eij,1) | i <- predecesseurs sj, let eij = fromJust $M.lookup (i,j) arcsMap] ++ 
               [(ejk,-1)| k <- successeurs sj, let ejk = fromJust $ M.lookup (j,k) arcsMap])
               `Equal` 0
             | j <- [s1 + 1.. sn -1], let sj = somm ! j]
       ctTot = ct1:ctn:cts      
   -- On minimise la somme des distances sur les arcs choisis
   liftModelLP $ setObj Minimize [(fromJust $ M.lookup arc arcsMap, dij) | (arc,dij) <- M.toList arcS]
   
   -- On alloue et on affecte les contraintes
   (c1:c2:ctr) <- liftModelLP $ newCtrs $ fromIntegral $ length ctTot
   liftModelLP $ forceCtr [c1] ct1
   liftModelLP $ forceCtr [c2] ctn
   liftModelLP $ foldM (\_ (ci,c) -> addConstraint ci c) Nothing  $ zip ctr cts
   
   -- On affecte des noms aux variables de décision importantes
   foldM (\_ ((i,j),eij) -> setDVarName eij ("E" ++ show i ++ "," ++ show j)) () (M.toList arcsMap)
   
   liftModelLP please
   return ()
