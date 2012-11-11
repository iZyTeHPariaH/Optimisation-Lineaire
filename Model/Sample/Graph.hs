module Model.Sample.Graph where

import qualified Data.Map as M
import Data.Array
import Control.Monad.State

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
