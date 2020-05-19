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

module Permutations.Permutations

import Permutations.SwapDown

%access public export
%default total

data Perm : {o : Type} -> List o -> List o -> Type where
  Nil : Perm [] []
  Ins : Perm xs ys -> SwapDown (a::ys) zs -> Perm (a::xs) zs

Uninhabited (Perm (x::xs) []) where
  uninhabited  Nil       impossible
  uninhabited (Ins _ sd) = uninhabited sd

insInjective: Ins {ys=ys1} p1 s1 = Ins {ys=ys2} p2 s2 -> (ys1 = ys2, p1 = p2, s1 = s2)
insInjective Refl = (Refl, Refl, Refl)

insCong5 : (xs1 = xs2) -> (ys1 = ys2) -> (zs1 = zs2) -> {p1 : Perm xs1 ys1} -> {p2 : Perm xs2 ys2} -> (p1 = p2)
       -> {s1 : SwapDown (a::ys1) zs1} -> {s2 : SwapDown (a::ys2) zs2} -> (s1 = s2)
       -> Ins {ys=ys1} p1 s1 = Ins {ys=ys2} p2 s2
insCong5 Refl Refl Refl Refl Refl = Refl

rewriteRight : cs = bs -> Perm as bs -> Perm as cs
rewriteRight Refl p = p

rewriteRightIgnore : {p1 : Perm as bs} -> {p2 : Perm cs ds} -> p1 = p2 -> rewriteRight prf p1 = p2
rewriteRightIgnore Refl {prf=Refl} = Refl

rewriteRightIgnoreR : {p1 : Perm as bs} -> {p2 : Perm cs ds} -> p1 = p2 -> p1 = rewriteRight prf p2
rewriteRightIgnoreR Refl {prf=Refl} = Refl

rewriteLeft : cs = as -> Perm as bs -> Perm cs bs
rewriteLeft Refl p = p

rewriteLeftIgnore : {p1 : Perm as bs} -> {p2 : Perm cs ds} -> p1 = p2 -> rewriteLeft prf p1 = p2
rewriteLeftIgnore Refl {prf=Refl} = Refl

rewriteLeftIgnoreR : {p1 : Perm as bs} -> {p2 : Perm cs ds} -> p1 = p2 -> p1 = rewriteLeft prf p2
rewriteLeftIgnoreR Refl {prf=Refl} = Refl

permId : (as : List o) -> Perm as as
permId []      = Nil
permId (a::as) = Ins (permId as) HereS

swap : (l : List o) -> (r : List o) -> Perm (l ++ r) (r ++ l)
swap []      r = rewriteRight (appendNilRightNeutral r) (permId r)
swap (l::ls) r = Ins (swap ls r) (swapDown r)

swapAddIdR : (l : List o) -> (r : List o) -> (t : List o) -> Perm (l ++ r ++ t) (r ++ l ++ t)
swapAddIdR []      r t = permId (r ++ t)
swapAddIdR (l::ls) r t = Ins (swapAddIdR ls r t) (swapDown r)

permAdd : Perm as bs -> Perm cs ds -> Perm (as ++ cs) (bs ++ ds)
permAdd       Nil        cd = cd
permAdd {ds} (Ins ab sw) cd = Ins (permAdd ab cd) (appended ds sw)

permAddIdL : (as : List o) -> Perm bs cs -> Perm (as ++ bs) (as ++ cs)
permAddIdL  []     bc = bc
permAddIdL (a::as) bc = Ins (permAddIdL as bc) HereS

shuffle : SwapDown as bs -> Perm bs cs -> Perm as cs
shuffle HereS p = p
shuffle (ThereS aab) (Ins by byc) =
  case shuffle aab by of
    Ins ax axy => case swComb axy byc of
      SW2 bxu auc => Ins (Ins ax bxu) auc

permComp : Perm as bs -> Perm bs cs -> Perm as cs
permComp  Nil         p  = p
permComp (Ins ab' sw) bc =
  case shuffle sw bc of
    Ins bc' sw' => Ins (permComp ab' bc') sw'

permCompCong5 : as1 = as2 -> bs1 = bs2 -> cs1 = cs2
            -> {p1 : Perm as1 bs1} -> {p2 : Perm as2 bs2} -> {p3 : Perm bs1 cs1} -> {p4 : Perm bs2 cs2}
            -> p1 = p2 -> p3 = p4 -> permComp p1 p3 = permComp p2 p4
permCompCong5 Refl Refl Refl Refl Refl = Refl

permAddCong6 : as1 = as2 -> bs1 = bs2 -> cs1 = cs2 -> ds1 = ds2
            -> {p1 : Perm as1 bs1} -> {p2 : Perm as2 bs2} -> {p3 : Perm cs1 ds1} -> {p4 : Perm cs2 ds2}
            -> p1 = p2 -> p3 = p4 -> permAdd p1 p3 = permAdd p2 p4
permAddCong6 Refl Refl Refl Refl Refl Refl = Refl

permAddIdLCong4 : as1 = as2 -> bs1 = bs2 -> cs1 = cs2
               -> {p1 : Perm bs1 cs1} -> {p2 : Perm bs2 cs2}
               -> p1 = p2 -> permAddIdL as1 p1 = permAddIdL as2 p2
permAddIdLCong4 Refl Refl Refl Refl = Refl

swapAddIdRCong3 : l1 = l2 -> r1 = r2 -> t1 = t2 -> swapAddIdR l1 r1 t1 = swapAddIdR l2 r2 t2
swapAddIdRCong3 Refl Refl Refl = Refl
