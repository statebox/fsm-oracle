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

---------------------------------
-- GoodHypergraphCat functions --
---------------------------------

infixr 4 ~+~>

||| GoodHypergraph signature
(~+~>) : {s : Type} -> {ai, ao : s -> List o} -> (a , b : List o) -> Type
(~+~>) a b {s} {ai} {ao} = Subset (Hypergraph s ai ao a b) GoodHypergraph

goodHypergraphCatCompose : {s : Type} -> {ai, ao : s -> List o} -> (a,b,c : List o)
    -> ((~+~>) {s} {ai} {ao} a b)
    -> ((~+~>) {s} {ai} {ao} b c)
    -> ((~+~>) {s} {ai} {ao} a c)
goodHypergraphCatCompose _ _ _ f g = Element (compose (getWitness f) (getWitness g)) (HComp (getProof f) (getProof g))

goodHypergraphCatComposeProof :  (a21 : List o) ->
       (b22 : List o) ->
       (c23 : List o) ->
       (d : List o) ->
       (f25 : Subset (Hypergraph sigma arityIn arityOut a21 b22)
                     GoodHypergraph) ->
       (g26 : Subset (Hypergraph sigma arityIn arityOut b22 c23)
                     GoodHypergraph) ->
       (h : Subset (Hypergraph sigma arityIn arityOut c23 d)
                   GoodHypergraph) ->
       Element (compose (getWitness f25)
                        (compose (getWitness g26) (getWitness h)))
               (HComp (getProof f25) (HComp (getProof g26) (getProof h))) =
       Element (compose (compose (getWitness f25) (getWitness g26))
                        (getWitness h))
               (HComp (HComp (getProof f25) (getProof g26)) (getProof h))
goodHypergraphCatComposeProof a b c d (Element f ff) (Element g gg) (Element h hh) =
  subsetEq (hgAssoc a b c d f g h)

goodHypergraphCat : (sigma : Type) -> (arityIn, arityOut : sigma -> List o) -> Category
goodHypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  ((~+~>) {s=sigma} {ai=arityIn} {ao=arityOut})
  (\n => Element (identity n) (Permutation (permId n)))
  goodHypergraphCatCompose
  (\a, b, (Element g gg) => subsetEq (hgLeftId a b g))
  (\a, b, (Element g gg) => subsetEq (hgRightId a b g))
  goodHypergraphCatComposeProof
goodSingleton : {s : Type} -> {ai, ao : s -> List o} -> (edge : s) -> mor (goodHypergraphCat s ai ao) (ai edge) (ao edge)
goodSingleton x = Element (Hypergraph.singleton x) (Singleton x)

goodPermutation : {s : Type} -> {ai, ao : s -> List o} -> Perm k m -> mor (goodHypergraphCat s ai ao) k m
goodPermutation p = Element (permutation p) (Permutation p)


------------------------------------
-- GoodHyperGraphTensor functions --
------------------------------------

tensorMor : (List o, List o) -> List o
tensorMor a = Basics.fst a ++ Basics.snd a

goodHypergraphTensorMor : {s : Type} -> {ai, ao : s -> List o} -> (a : (List o, List o))
     -> (b : (List o, List o))
     -> (ProductMorphism (goodHypergraphCat s ai ao)
                         (goodHypergraphCat s ai ao) a b)
     -> mor (goodHypergraphCat s ai ao) (tensorMor a) (tensorMor b)
goodHypergraphTensorMor a b f =
  Element (add (Subset.getWitness $ pi1 f) (Subset.getWitness $ pi2 f) {k=fst a} {l=fst b} {m=snd a} {n=snd b})
          (VComp (getProof $ pi1 f) (getProof $ pi2 f))

goodHypergraphTensorCompose : (a, b, c : (List o, List o)) ->
        (f : ProductMorphism (goodHypergraphCat s ai ao) (goodHypergraphCat s ai ao) a b) ->
        (g : ProductMorphism (goodHypergraphCat s ai ao) (goodHypergraphCat s ai ao) b c) ->
        goodHypergraphTensorMor a c
            (productCompose a b c f g) =
            goodHypergraphCatCompose
                (tensorMor a)
                (tensorMor b)
                (tensorMor c)
                (goodHypergraphTensorMor a b f)
                (goodHypergraphTensorMor b c g)
goodHypergraphTensorCompose a b c f g =
  subsetEq (hgPreserveCompose a b c (MkProductMorphism (getWitness $ pi1 f) (getWitness $ pi2 f))
                                    (MkProductMorphism (getWitness $ pi1 g) (getWitness $ pi2 g)))
goodHyperGraphTensor : (s : Type) -> (ai, ao : s -> List o) ->
                       CFunctor (productCategory (goodHypergraphCat s ai ao) (goodHypergraphCat s ai ao))
                                (goodHypergraphCat s ai ao)
goodHyperGraphTensor s ai ao = MkCFunctor
  tensorMor
  goodHypergraphTensorMor
  (\a => subsetEq (hgPreserveId (fst a) (snd a)))
  goodHypergraphTensorCompose

postulate
composeGoodHypergraphProof : (a, b, c : List o) ->
                      (d, e, f : List o) ->
                      (g : Subset (Hypergraph s ai ao a b) GoodHypergraph) ->
                      (h : Subset (Hypergraph s ai ao c d) GoodHypergraph) ->
                      (k : Subset (Hypergraph s ai ao e f) GoodHypergraph) ->
                      Element (add (getWitness g) (add (getWitness h) (getWitness k)))
                              (VComp (getProof g) (VComp (getProof h) (getProof k))) =
                      Element (add (add (getWitness g) (getWitness h)) (getWitness k))
                              (VComp (VComp (getProof g) (getProof h)) (getProof k))
composeGoodHypergraphProof fi fo gi go hi ho (Element f ff) (Element g gg) (Element h hh) = ?what -- subsetEq (hgTensorAssociative fi fo gi go hi ho f g h))

goodHypergraphSMC : (sigma : Type) -> (arityIn, arityOut : sigma -> List o) -> StrictMonoidalCategory
goodHypergraphSMC s ai ao = MkStrictMonoidalCategory
  (goodHypergraphCat s ai ao)
  (goodHyperGraphTensor s ai ao)
  []
  (\as => Refl)
  (\as => appendNilRightNeutral as)
  appendAssociative
  composeGoodHypergraphProof
