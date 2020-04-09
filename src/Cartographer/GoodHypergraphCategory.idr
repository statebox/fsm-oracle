module Cartographer.GoodHypergraphCategory

import Data.List

import Basic.Category
import Basic.Functor
import MonoidalCategory.StrictMonoidalCategory
import Product.ProductCategory

import Permutations.SwapDown
import Permutations.Permutations
import Permutations.PermutationsCategory
import Permutations.PermutationsStrictMonoidalCategory

import Cartographer.Hypergraph as HG
import Cartographer.HypergraphCategory
import Cartographer.HypergraphStrictMonoidalCategory

%access public export

data GoodHypergraph : {s : Type} -> {ai, ao : s -> List o} -> (g : Hypergraph s ai ao k l) -> Type where
    Singleton : (edge : s) -> GoodHypergraph (singleton edge)
    Permutation : (p : Perm k l) -> GoodHypergraph (permutation p)
    HComp : (a : GoodHypergraph g)
         -> (b : GoodHypergraph h)
         -> GoodHypergraph (compose g h)
    VComp : (a : GoodHypergraph g)
         -> (b : GoodHypergraph h)
         -> GoodHypergraph (add g h)

getHypergraph : {g : Hypergraph s ai ao k l} -> GoodHypergraph g -> Hypergraph s ai ao k l
getHypergraph _ {g} = g

postulate subsetEq : Subset.getWitness g = Subset.getWitness h -> g = h

goodHypergraphCat : (sigma : Type) -> (arityIn, arityOut : sigma -> List o) -> Category
goodHypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  (\k, l => Subset (Hypergraph sigma arityIn arityOut k l) GoodHypergraph)
  (\n => Element (identity n) (Permutation (permId n)))
  (\_,_,_,f,g => Element (compose (getWitness f) (getWitness g)) (HComp (getProof f) (getProof g)))
  (\a, b, (Element g gg) => subsetEq (hgLeftId a b g))
  (\a, b, (Element g gg) => subsetEq (hgRightId a b g))
  (\a, b, c, d, (Element f ff), (Element g gg), (Element h hh) => subsetEq (hgAssoc a b c d f g h))

goodSingleton : {s : Type} -> {ai, ao : s -> List o} -> (edge : s) -> mor (goodHypergraphCat s ai ao) (ai edge) (ao edge)
goodSingleton x = Element (Hypergraph.singleton x) (Singleton x)

goodPermutation : {s : Type} -> {ai, ao : s -> List o} -> Perm k m -> mor (goodHypergraphCat s ai ao) k m
goodPermutation p = Element (permutation p) (Permutation p)

goodHyperGraphTensor : (s : Type) -> (ai, ao : s -> List o) -> CFunctor (productCategory (goodHypergraphCat s ai ao) (goodHypergraphCat s ai ao)) (goodHypergraphCat s ai ao)
goodHyperGraphTensor s ai ao = MkCFunctor
  (\a => fst a ++ snd a)
  (\a, b, f => Element (add (getWitness $ pi1 f) (getWitness $ pi2 f) {k=fst a} {l=fst b} {m=snd a} {n=snd b}) (VComp (getProof $ pi1 f) (getProof $ pi2 f)))
  (\a => subsetEq (hgPreserveId (fst a) (snd a)))
  (\a, b, c, f, g => subsetEq (hgPreserveCompose a b c (MkProductMorphism (getWitness $ pi1 f) (getWitness $ pi2 f)) (MkProductMorphism (getWitness $ pi1 g) (getWitness $ pi2 g))))

goodHypergraphSMC : (sigma : Type) -> (arityIn, arityOut : sigma -> List o) -> StrictMonoidalCategory
goodHypergraphSMC s ai ao = MkStrictMonoidalCategory
  (goodHypergraphCat s ai ao)
  (goodHyperGraphTensor s ai ao)
  []
  (\as => Refl)
  (\as => appendNilRightNeutral as)
  appendAssociative
  ?proofgoodhypergraph -- (\fi, fo, gi, go, hi, ho, (Element f ff), (Element g gg), (Element h hh) => subsetEq (hgTensorAssociative fi fo gi go hi ho f g h))
