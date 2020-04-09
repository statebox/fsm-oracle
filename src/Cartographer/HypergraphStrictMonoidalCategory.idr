module Cartographer.HypergraphStrictMonoidalCategory

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

%access public export
%default total

hgPreserveId : {s : Type} -> {ai, ao : s -> List o} -> (as, bs : List o)
            -> add (identity {s} {ai} {ao} as) (identity {s} {ai} {ao} bs) = identity {s} {ai} {ao} (as ++ bs)
hgPreserveId {s} {ai} {ao} as bs with (identity {s} {ai} {ao} as)
  | MkHypergraph ta pa with (identity {s} {ai} {ao} bs)
    | MkHypergraph tb pb = hgCong2 Refl $
      permCompCong5 Refl Refl Refl
        Refl
        (permCompCong5 Refl Refl Refl
          (permPreserveId as bs)
          (swapAddIdRNilRightNeutral as bs)
        `trans` permCompLeftId (permId (as ++ bs)))
      `trans` permCompLeftId (permId (as ++ bs))

hgPreserveCompose : {s : Type} -> {ai, ao : s -> List o} -> (a, b, c : (List o, List o))
                 -> (f : ProductMorphism (hypergraphCat s ai ao) (hypergraphCat s ai ao) a b)
                 -> (g : ProductMorphism (hypergraphCat s ai ao) (hypergraphCat s ai ao) b c)
                 -> add (compose (pi1 f) (pi1 g)) (compose (pi2 f) (pi2 g))
                  = compose (add (pi1 f) (pi2 f)) (add (pi1 g) (pi2 g))
hgPreserveCompose a b c
  (MkProductMorphism (MkHypergraph pf1 sf1) (MkHypergraph pf2 sf2))
  (MkProductMorphism (MkHypergraph pg1 sg1) (MkHypergraph pg2 sg2))
  = hypergraphEq p ?w
  where
    p : Perm ((pf1 ++ pg1) ++ (pf2 ++ pg2)) ((pf1 ++ pf2) ++ (pg1 ++ pg2))
    p = rewriteLeft (sym $ appendAssociative pf1 pg1 (pf2 ++ pg2)) $
        rewriteRight (sym $ appendAssociative pf1 pf2 (pg1 ++ pg2)) $
        pf1 `permAddIdL` swapAddIdR pg1 pf2 pg2

hgTensor : (s : Type) -> (ai, ao : s -> List o) -> CFunctor (productCategory (hypergraphCat s ai ao) (hypergraphCat s ai ao)) (hypergraphCat s ai ao)
hgTensor s ai ao = MkCFunctor
  (\a => fst a ++ snd a)
  (\a, b, f => add (pi1 f) (pi2 f) {k=fst a} {l=fst b} {m=snd a} {n=snd b})
  (\a => hgPreserveId (fst a) (snd a))
  hgPreserveCompose

hgTensorAssociative : {s : Type} -> {ai, ao : s -> List o}
  -> (fi, fo, gi, go, hi, ho: List o)
  -> (f : Hypergraph s ai ao fi fo) -> (g : Hypergraph s ai ao gi go) -> (h : Hypergraph s ai ao hi ho)
  -> add f (add g h) = add (add f g) h

hypergraphSMC : (s : Type) -> (ai, ao : s -> List o) -> StrictMonoidalCategory
hypergraphSMC s ai ao = MkStrictMonoidalCategory
  (hypergraphCat s ai ao)
  (hgTensor s ai ao)
  []
  (\as => Refl)
  (\as => appendNilRightNeutral as)
  appendAssociative
  hgTensorAssociative
