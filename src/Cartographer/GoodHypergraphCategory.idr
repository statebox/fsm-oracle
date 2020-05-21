{-

SPDX-License-Identifier: AGPL-3.0-only

This file is part of `statebox/fsm-oracle`.

Copyright (C) 2020 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.

-}

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

goodHypergraphCatComposeProof : (a, b, c, d : List o) ->
                                (f : Subset (Hypergraph sigma arityIn arityOut a b) GoodHypergraph) ->
                                (g : Subset (Hypergraph sigma arityIn arityOut b c) GoodHypergraph) ->
                                (h : Subset (Hypergraph sigma arityIn arityOut c d) GoodHypergraph) ->
                                Element (compose (getWitness f) (compose (getWitness g) (getWitness h)))
                                        (HComp (getProof f) (HComp (getProof g) (getProof h))) =
                                Element (compose (compose (getWitness f) (getWitness g)) (getWitness h)) (HComp (HComp (getProof f) (getProof g)) (getProof h))
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
  subsetEq (hgPreserveCompose a b c (MkProductMorphism (Subset.getWitness $ pi1 f) (Subset.getWitness $ pi2 f))
                                    (MkProductMorphism (Subset.getWitness $ pi1 g) (Subset.getWitness $ pi2 g)))
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
                      Element (add (Subset.getWitness g) (add (Subset.getWitness h) (Subset.getWitness k)))
                              (VComp (getProof g) (VComp (getProof h) (getProof k))) =
                      Element (add (add (Subset.getWitness g) (Subset.getWitness h)) (Subset.getWitness k))
                              (VComp (VComp (getProof g) (getProof h)) (getProof k))

goodHypergraphSMC : (sigma : Type) -> (arityIn, arityOut : sigma -> List o) -> StrictMonoidalCategory
goodHypergraphSMC s ai ao = MkStrictMonoidalCategory
  (goodHypergraphCat s ai ao)
  (goodHyperGraphTensor s ai ao)
  []
  (\as => Refl)
  (\as => appendNilRightNeutral as)
  appendAssociative
  composeGoodHypergraphProof
