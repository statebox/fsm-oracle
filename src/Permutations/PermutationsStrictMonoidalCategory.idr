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

module Permutations.PermutationsStrictMonoidalCategory

import Basic.Category
import Basic.Functor
import MonoidalCategory.StrictMonoidalCategory
import Product.ProductCategory

import Permutations.SwapDown
import Permutations.Permutations
import Permutations.PermutationsCategory

%access public export
%default total

permPreserveId : (as, bs : List o) -> permAdd (permId as) (permId bs) = permId (as ++ bs)
permPreserveId     []  bs = Refl
permPreserveId (a::as) bs = insCong5 Refl Refl Refl (permPreserveId as bs) Refl

permAddIdLPreserveId : (as, bs : List o) -> permAddIdL as (permId bs) = permId (as ++ bs)
permAddIdLPreserveId     []  bs = Refl
permAddIdLPreserveId (a::as) bs = insCong5 Refl Refl Refl (permAddIdLPreserveId as bs) Refl

permAddIdLAppend : (as, bs : List o) -> (p : Perm cs ds) -> permAddIdL (as ++ bs) p = permAddIdL as (permAddIdL bs p)
permAddIdLAppend [] bs p = Refl
permAddIdLAppend (a::as) bs p {cs} {ds} = let abd = sym $appendAssociative as bs ds in
  insCong5 (sym $ appendAssociative as bs cs) abd (cong abd) (permAddIdLAppend as bs p) (congHereS abd)

permAddIdLCompDist : (as : List o) -> (p : Perm bs cs) -> (q : Perm cs ds) -> permAddIdL as (p `permComp` q) = permAddIdL as p `permComp` permAddIdL as q
permAddIdLCompDist [] p q = Refl
permAddIdLCompDist (a::as) p q = insCong5 Refl Refl Refl (permAddIdLCompDist as p q) Refl

permAddNilRightNeutral : (ab : Perm as bs) -> permAdd ab Nil = ab
permAddNilRightNeutral              Nil          = Refl
permAddNilRightNeutral {as=a::as1} {bs} (Ins {ys} p s) =
  insCong5 (appendNilRightNeutral as1)
          (appendNilRightNeutral ys)
          (appendNilRightNeutral bs)
          (permAddNilRightNeutral p)
          (appendedNilNeutral s)

magic : {ys : List t} -> SwapDown (a1 :: ys) cs1 -> List t
magic _ {ys} = ys

postulate
permPreserveCompose : (a, b, c : (List o, List o))
                   -> (f : ProductMorphism (permutationsCat o) (permutationsCat o) a b)
                   -> (g : ProductMorphism (permutationsCat o) (permutationsCat o) b c)
                   -> permAdd (permComp (pi1 f) (pi1 g)) (permComp (pi2 f) (pi2 g))
                    = permComp (permAdd (pi1 f) (pi2 f)) (permAdd (pi1 g) (pi2 g))
-- permPreserveCompose (_, _) (_, _) (_, _) (MkProductMorphism Nil f2) (MkProductMorphism Nil g2) = Refl
-- permPreserveCompose (as, _) (bs, _) (cs, _) (MkProductMorphism f1 Nil) (MkProductMorphism g1 Nil) =
--   trans (permAddNilRightNeutral (permComp f1 g1)) $ permCompCong5
--     (sym $ appendNilRightNeutral as)
--     (sym $ appendNilRightNeutral bs)
--     (sym $ appendNilRightNeutral cs)
--     (sym $ permAddNilRightNeutral f1)
--     (sym $ permAddNilRightNeutral g1)
-- permPreserveCompose (a1::as1, a2::as2) ([], []) (cs1,cs2) (MkProductMorphism f1 f2) (MkProductMorphism g1 g2) = absurd f1
-- permPreserveCompose (a1::as1, as2) (a1::ys1, bs2) (cs1, cs2)
--     (MkProductMorphism (Ins pf1 HereS) fs) (MkProductMorphism (Ins g1 gs1) gs) {o} = cong
--       {f=\x => Ins x (appended cs2 gs1)} $
--         permPreserveCompose (as1, as2) (ys1, bs2) (magic {t=o} gs1, cs2) (MkProductMorphism pf1 fs) (MkProductMorphism g1 gs)
-- permPreserveCompose (a1::as1, as2) (b1::bs1, bs2) (cs1, cs2)
--     (MkProductMorphism (Ins pf1 (ThereS fs1)) fs) (MkProductMorphism (Ins g1 gs1) gs) {o} = ?y1
-- permPreserveCompose (as1, a2::as2) (bs1, b2::bs2) (cs1, cs2)
--     (MkProductMorphism fs (Ins pf2 sf2)) (MkProductMorphism gs (Ins pg2 sg2)) = ?y2
-- permPreserveCompose _ _ _ _ _ = ?catchAll

permTensor : (o : Type) -> CFunctor (productCategory (permutationsCat o) (permutationsCat o)) (permutationsCat o)
permTensor _ = MkCFunctor
  (\a => fst a ++ snd a)
  (\a, b, f => permAdd (pi1 f) (pi2 f) {as=fst a} {bs=fst b} {cs=snd a} {ds=snd b})
  (\a => permPreserveId (fst a) (snd a))
  permPreserveCompose

permAddAssociativeMor : (pab : Perm as bs) -> (pcd : Perm cs ds) -> (pef : Perm es fs)
                     -> permAdd pab (permAdd pcd pef) = permAdd (permAdd pab pcd) pef
permAddAssociativeMor Nil _ _ = Refl
permAddAssociativeMor {as=a::as} {bs} {cs} {ds} {es} {fs} (Ins {ys} pab s) pcd pef = insCong5
  (appendAssociative as cs es)
  (appendAssociative ys ds fs)
  (appendAssociative bs ds fs)
  (permAddAssociativeMor pab pcd pef)
  (appendedAppendDistr ds fs s)

permutationsSMC : (o : Type) -> StrictMonoidalCategory
permutationsSMC o = MkStrictMonoidalCategory
  (PermutationsCategory.permutationsCat o)
  (permTensor o)
  []
  (\as => Refl)
  (\as => appendNilRightNeutral as)
  appendAssociative
  (\_, _, _, _, _, _ => permAddAssociativeMor)


-- for symmetric monoidal category
swapAddEq : (as, bs, cs : List o) -> swapAddIdR as bs cs = swap as bs `permAdd` permId cs
swapAddEq [] [] cs = Refl
swapAddEq [] bs cs = sym (permPreserveId bs cs) `trans` permAddCong6 Refl (sym $ appendNilRightNeutral bs) Refl Refl (rewriteRightIgnoreR Refl) Refl
swapAddEq (a::as) bs cs = insCong5 (appendAssociative as bs cs) (appendAssociative bs as cs) (appendAssociative bs (a::as) cs) (swapAddEq as bs cs) (swapDownAppendedNeutral bs _ cs)

swapNilRightNeutral : (l : List o) -> swap l [] = permId l
swapNilRightNeutral [] = Refl
swapNilRightNeutral (l::ls) = insCong5 (appendNilRightNeutral ls) Refl Refl (swapNilRightNeutral ls) Refl

swapAddIdRNilRightNeutral : (l : List o) -> (k : List o) -> swapAddIdR l [] k = permId (l ++ k)
swapAddIdRNilRightNeutral [] k = Refl
swapAddIdRNilRightNeutral (l::ls) k = insCong5 Refl Refl Refl (swapAddIdRNilRightNeutral ls k) Refl

--\/-----    --\/---}
--/\-\/-- = {--/\/--}
-----/\--   {---/\--
swapHexagonal1 : (as, bs, cs : List o) ->
  swapAddIdR as bs cs `permComp` permAddIdL bs (swap as cs) = swap as (bs ++ cs)

swapHexagonal1' : (as, bs, cs, ds : List o) ->
  swapAddIdR as bs (cs ++ ds) `permComp` permAddIdL bs (swapAddIdR as cs ds) = swapAddIdR as (bs ++ cs) ds

-----\/--   {---\/--
--\/-/\-- = {--\/\--}
--/\-----    --/\---}
swapHexagonal2 : (as, bs, cs : List o) ->
  permAddIdL as (swap bs cs) `permComp` swapAddIdR as cs bs = swap (as ++ bs) cs

swapHexagonal2' : (as, bs, cs, ds : List o) ->
  permAddIdL as (swapAddIdR bs cs ds) `permComp` swapAddIdR as cs (bs ++ ds) = swapAddIdR (as ++ bs) cs ds

--p-\/-- = --\/----
----/\--   --/\-p--
swapNatural : (as, bs, cs : List o) -> (p : Perm as bs) ->
  (p `permAdd` permId cs) `permComp` swap bs cs = swap as cs `permComp` permAddIdL cs p

swapNatural' : (as, bs, cs, ds : List o) -> (p : Perm as bs) ->
  (p `permAdd` permId (cs ++ ds)) `permComp` swapAddIdR bs cs ds = swapAddIdR as cs ds `permComp` permAddIdL cs (p `permAdd` permId ds)

-----\/-----   --\/----\/--
--\/-/\-\/-- = --/\-\/-/\--
--/\----/\--   -----/\-----
swap3' : (as, bs, cs, ds : List o)
  -> (permAddIdL as (swapAddIdR bs cs ds) `permComp` swapAddIdR as cs (bs ++ ds)) `permComp` permAddIdL cs (swapAddIdR as bs ds)
     = swapAddIdR as bs (cs ++ ds) `permComp` (permAddIdL bs (swapAddIdR as cs ds) `permComp` swapAddIdR bs cs (as ++ ds))
swap3' as bs cs ds =
  trans (permCompCong5 (appendAssociative as bs (cs ++ ds))
                       (cong {f=\z=>cs++z} (appendAssociative as bs ds))
                       (cong {f=\z=>cs++z} (appendAssociative bs as ds))
                       (swapHexagonal2' as bs cs ds)
                       (permAddIdLCong4 Refl
                                        (appendAssociative as bs ds)
                                        (appendAssociative bs as ds)
                                        (swapAddEq as bs ds)))
        (trans (sym $ swapNatural' (as ++ bs) (bs ++ as) cs ds (swap as bs))
               (permCompCong5 (sym $ appendAssociative as bs (cs ++ ds))
                              (sym $ appendAssociative bs as (cs ++ ds))
                              (cong {f=\z=>cs++z} (sym $ appendAssociative bs as ds))
                              (sym $ swapAddEq as bs (cs ++ ds))
                              (sym $ swapHexagonal2' bs as cs ds)))
