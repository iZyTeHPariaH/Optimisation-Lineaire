module Solve.IP.BranchBound
where
import Control.Monad.Cont
import Debug.Trace
import Data.List
data OptCriteria = Max | Min -- Critères d'optimisation

class OptNode n where
  trivial :: n -> Bool     -- Prédicat vérifiant si on est sur une feuille.
  solve ::  n -> Double  -- Fonction résolvant un problème (une feuille).
  
branchbound :: (Show n, OptNode n) =>  (n -> [n]) -- Séparation du noeud
                           -> (n -> Double)   -- Approximation du noeud (borne optimale non realisable)
                           -> (n -> Double)   -- Approximation du noeud (borne non optimale realisable)
                           -> n          -- Noeud initial
                           -> (n,Double)      -- Couple (Noeud optimal, valeur optimale) trouvé
                           -> OptCriteria -- Critère d'optimisation
                           
                           -> Cont r (n,Double) -- Couple (Noeud optimal, valeur optimale) trouvé dans l'arbre
                                  
branchbound branch borne eval initN opt@(optimum,optval) criteria 
     -- Si on ne peut pas espérer trouver mieux dans l'arbre, on abandonne la recherche.
     | not $ maxval `better` optval = return (optimum,optval)
    
     -- Si on se trouve dans une feuille de l'arbre, on calcule sa valeur et on la 
     -- compare à l'optimum local actuel avant de la conserver si elle est meilleure.
     | trivial initN    = if initVal `better` optval                      
                          then return (initN, initVal)
                          else return opt
                             
     -- Si on se trouve dans un noeud, et qu'on peut esperer trouver mieux, on le développe
     -- et on poursuit l'exploration dans ses fils
     | maxval `better` minval =  -- trace ("[*] " ++ "[NR= " ++ show maxval ++ ",R= "++ show minval ++ ",trouve=" ++ show optval ++ "] - Branching on " ++ show initN)
                                      (foldM (\a e -> branchbound branch borne eval e a criteria) opt (branch initN) )
                          
     -- Sinon, si on est sur que le noeud contient une solution optimale, on ne l'explore pas et on
     -- le retourne
     | otherwise        = return (initN,minval)
 where minval = eval initN
       maxval = borne initN
       initVal = solve initN        
        -- La fonctions de comparaison better est définie en fonction du critère choisi.
       better :: (Ord t) => t -> t -> Bool
       better = case criteria of
          Min -> (<)
          Max -> (>)
        
          
astar :: (OptNode n) => (n -> [n]) -- Fonction de séparation
                     -> (n -> n -> Bool) -- Heursitique comparant deux problèmes et renvoyant "Vrai" 
                                         -- s'il faut choisir la première solution plutot que la seconde
                     -> n -- Noeud initial
                     -> (n,Double) -- Couple (Noeud trouvé, valeur obtenue)
                                
astar branch heuristique initN 
 | trivial initN = (initN, solve initN)
 | otherwise     = let candidats = branch initN
                       meilleurCandidat = foldl1 (\a e -> if a `heuristique` e then a else e) candidats in           
                   astar branch heuristique meilleurCandidat



