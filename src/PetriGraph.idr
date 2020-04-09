module PetriGraph

import Data.Vect
import Basic.Category
import Basic.Functor
import Product.ProductCategory
import Permutations.Permutations
import Permutations.SwapDown
import Cartographer.Hypergraph
import Cartographer.GoodHypergraphCategory
import Cartographer.HypergraphStrictMonoidalCategory
import MonoidalCategory.StrictMonoidalCategory


%default total

public export
record PetriSpec (k : Nat) where
  constructor MkPetriSpec
  Places : Nat
  Edges : Vect k (List (Fin Places), List (Fin Places))

public export
data Tree o m = Tensor (Tree o m) (Tree o m)
              | Sequence (Tree o m) (Tree o m)
              | Sym o o
              | Id o
              | Mor m

public export
PetriState : PetriSpec k -> Type
PetriState spec = List (Fin (Places spec))

public export
PetriPath : Nat -> Nat -> Type
PetriPath places k = Tree (Fin places) (Fin k)

public export
record PetriExec where
  constructor MkPetriExec
  Spec : PetriSpec k
  Path : PetriPath (Places Spec) k
  State : PetriState Spec


public export
Domain : (morphisms : Vect k (List a, List a)) -> Tree a (Fin k) -> List a
Domain m (Tensor l r) = (Domain m l) ++ (Domain m r)
Domain m (Sequence l r) = Domain m l
Domain m (Id o) = pure o
Domain m (Sym l r) = [l, r]
Domain m (Mor i) = fst $ index i m

public export
Codomain : (morphisms : Vect k (List a, List a)) -> Tree a (Fin k) -> List a
Codomain m (Tensor l r) = Codomain m l ++ Codomain m r
Codomain m (Sequence l r) = Codomain m r
Codomain m (Id o) = pure o
Codomain m (Sym l r) = [r, l]
Codomain m (Mor i) = snd $ index i m

export
checkTree : (spec : PetriSpec k) -> Tree Nat Nat -> Maybe (PetriPath (Places spec) k)
checkTree spec (Tensor x y) = [| Tensor (checkTree spec x) (checkTree spec y) |]
checkTree spec (Sequence x y) = [| Sequence (checkTree spec x) (checkTree spec y) |]
checkTree spec (Sym x y) = [| Sym (natToFin x (Places spec)) (natToFin y (Places spec)) |]
checkTree spec (Id x) = Id <$> natToFin x (Places spec)
checkTree spec (Mor x) {k} = Mor <$> natToFin x k


public export
goodPetriSMC : (spec : PetriSpec k) -> StrictMonoidalCategory
goodPetriSMC spec = goodHypergraphSMC (Fin k)
                                      (\m => fst $ index m (Edges spec))
                                      (\m => snd $ index m (Edges spec))

goodMapping : (spec : PetriSpec k) -> (path : PetriPath (Places spec) k)
           -> Maybe (mor (cat (goodPetriSMC spec))
                         (Domain (Edges spec) path)
                         (Codomain (Edges spec) path))
goodMapping s (Tensor x y) = do
  x' <- goodMapping s x
  y' <- goodMapping s y
  pure $ mapMor (tensor (goodPetriSMC s))
                (Domain (Edges s) x, Domain (Edges s) y)
                (Codomain (Edges s) x, Codomain (Edges s) y)
                (MkProductMorphism x' y')
goodMapping s (Sequence x y) {k} = do
  x' <- goodMapping s x
  y' <- goodMapping s y
  case decEq (Domain (Edges s) y) (Codomain (Edges s) x) of
       Yes p =>  let y'' = replace
                              {P = (\newDom => Subset (Hypergraph (Fin k)
                                                 (\m => fst $ index m (Edges s))
                                                 (\m => snd $ index m (Edges s))
                                                 newDom
                                                 (Codomain (Edges s) y))
                                                 GoodHypergraph)
                              }
                              p y'
                  in pure $ compose (cat (goodPetriSMC s)) _ _ _ x' y''
       No _ => Nothing
goodMapping s (Id x) = Just $ identity (cat (goodPetriSMC s)) [x]
goodMapping s (Sym a b) = Just $ goodPermutation (swap [a] [b])
goodMapping s (Mor x) = Just $ goodSingleton x

export
composeWithId : (spec : PetriSpec k) -> (path : PetriPath (Places spec) k)
             -> (state : PetriState spec)
             -> Maybe (mor (cat (goodPetriSMC spec))
                           (state)
                           (Codomain (Edges spec) path))
composeWithId spec path state with (decEq state (Domain (Edges spec) path))
  composeWithId spec path state | Yes prf = rewrite prf in goodMapping spec path
  composeWithId spec path state | No _ = Nothing
