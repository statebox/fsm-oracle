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

module Permutations.PermutationsCategory

import Basic.Category

import Permutations.SwapDown
import Permutations.Permutations

%access public export
%default total

permCompLeftId : (ab : Perm as bs) -> permComp (permId as) ab = ab
permCompLeftId  Nil         = Refl
permCompLeftId (Ins ab' sw) = cong {f=\p => Ins p sw} (permCompLeftId ab')

shuffleId : (aab : SwapDown (a::as) bs) -> shuffle aab (permId bs) = Ins (permId as) aab
shuffleId  HereS      = Refl
shuffleId (ThereS {bs} aab) with (shuffle aab (permId bs)) proof shprf
  | Ins ay ayb = case insInjective $ trans shprf (shuffleId aab) of (Refl, Refl, Refl) => Refl

permCompRightId : (ab : Perm as bs) -> permComp ab (permId bs) = ab
permCompRightId  Nil                 = Refl
permCompRightId {bs} (Ins ab' sw) with (shuffle sw (permId bs)) proof shprf
  | Ins bc' sw' = case insInjective $ trans shprf (shuffleId sw) of
    (Refl, Refl, Refl) => rewrite permCompRightId ab' in Refl

flipShuffle : Perm as bs -> SwapDown bs cs -> Perm as cs
flipShuffle Nil swap {cs=[]}= Nil
flipShuffle Nil swap {cs=(x :: xs)} impossible
flipShuffle (Ins p HereS) swap = Ins p swap
flipShuffle (Ins p (ThereS s)) swap =
  case swComb s swap of SW2 sw1 sw2 => Ins (flipShuffle p sw1) sw2


assocShuffle : (s1 : SwapDown as bs) -> (p : Perm bs cs) -> (s2 : SwapDown cs ds) ->
               shuffle s1 (flipShuffle p s2) = flipShuffle (shuffle s1 p) s2


postulate
shuffleComp : (abb : SwapDown as bs) -> (bc : Perm bs cs) -> (cd : Perm cs ds)
           -> Ins bc' ayc = shuffle abb bc
           -> Ins {ys=ds1} cd' ad1d = shuffle ayc cd
           -> Ins {ys=ds2} bd' ad2d = shuffle abb (permComp bc cd)
           -> (ds1 = ds2, ad1d = ad2d, bd' = permComp bc' cd')
shuffleComp  sw (Ins p1 sw1) (Ins p2 sw2) prf1 prf2 prf3 {bd'} {bc'} {cd'} = ?shuffHole
 -- let p = the (bd' = permComp bc' cd') (assocShuffle ?sw1 ?pe1 ?sw2) in ?shuff
--shuffleComp {ds} (ThereS aab) (Ins {ys=zs} bz bzc) cd eq1  eq2 eq3 with (shuffle aab bz) proof bcPrf
--  | Ins {ys=xs} ax axz with (shuffle bzc cd)
--    | Ins {ys=us} zu bud with (shuffle aab (permComp bz zu)) proof bdPrf
--      | Ins {ys=ts} at atu with (shuffle axz zu) proof cdPrf
--        | Ins {ys=qs} xq aqu with (shuffleComp aab bz zu bcPrf cdPrf bdPrf)
--          | (r1, r2, r3) with (swComb axz bzc)
--            | SW2 {ys=ws} bxw awc with (eq1)
--              | Refl with (shuffle awc cd)
--                | Ins {ys=vs} wv avd with (eq2)
--                  | Refl with (swComb atu bud)
--                    | SW2 {ys=ss} bts asd with (eq3)
--                      | Refl with (shuffle bxw wv)
--                        | Ins {ys=rs} xr brv = ?pleaseLeaveMeAlone
-- vs = ss
-- avd = asd
-- rs = ts
-- brv = bts

-- need to proof something about swComb...
-- swComb axz bzc = SW2 bxw awc, shuffle awc cd = Ins wv avd
-- swComb atu bud = SW2 bts asd, shuffle bxw wv = Ins xr brv

-- shuffleComp  _ _ _  _    _    _    = ?catchall

permAssoc : (ab : Perm aas bbs) -> (bc : Perm bbs ccs) -> (cd : Perm ccs dds)
         -> permComp ab (permComp bc cd) = permComp (permComp ab bc) cd
permAssoc Nil bc cd = Refl
permAssoc (Ins {xs=as} {ys=bs} ab' abb) bc cd with (shuffle abb (permComp bc cd)) proof bdPrf
  | Ins {ys=ds} bd' add with (shuffle abb bc) proof bcPrf
    | Ins {ys=cs} bc' acc with (shuffle acc cd) proof cdPrf
      | Ins {ys=ds'} cd' ad'd =
        let (Refl, Refl, Refl) = shuffleComp abb bc cd bcPrf cdPrf bdPrf in
        insCong5 Refl Refl Refl (permAssoc ab' bc' cd') Refl

permutationsCat : (o : Type) -> Category
permutationsCat o = MkCategory
  (List o)
  Perm
  permId
  (\as, bs, cs => permComp {as} {bs} {cs})
  (\_, _ => permCompLeftId)
  (\_, _ => permCompRightId)
  (\_, _, _, _ => permAssoc)
