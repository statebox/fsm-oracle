module Cartographer.HypergraphCategory

import Data.List

import Basic.Category

import Permutations.SwapDown
import Permutations.Permutations
import Permutations.PermutationsCategory
import Permutations.PermutationsStrictMonoidalCategory

import Cartographer.Hypergraph

%access public export
%default total

hgCong2 : {s : Type} -> {ai, ao : s -> List o} -> {k : List o}
       -> {t1 : List s} -> {t2 : List s} -> (t1 = t2)
       -> {w1 : Perm (sumArity ao t1 ++ k) (sumArity ai t1 ++ m)}
       -> {w2 : Perm (sumArity ao t2 ++ k) (sumArity ai t2 ++ m)}
       -> (w1 = w2) -> MkHypergraph t1 w1 = MkHypergraph t2 w2
hgCong2 Refl Refl = Refl

wl : {ai, ao : s -> List o} -> {t : List s} -> (k, l : List o) -> {w : Perm (sumArity ao t ++ k) (sumArity ai t ++ l)}
  -> permComp (permComp (permAddIdL (sumArity ao t) (permId k))
                        (swapAddIdR (sumArity ao t) [] k))
              (permComp w (permId (sumArity ai t ++ l))) =
     w
wl {ao} {t} k _ {w} =
  permCompCong5 Refl Refl Refl
    (permCompCong5 Refl Refl Refl
      (permAddIdLPreserveId (sumArity ao t) k)
      (swapAddIdRNilRightNeutral (sumArity ao t) k)
    `trans` permCompLeftId (permId (sumArity ao t ++ k)))
    (permCompRightId w)
  `trans` permCompLeftId w

wr : {ai, ao : s -> List o} -> {t : List s} -> (k, l : List o) -> {w : Perm (sumArity ao t ++ k) (sumArity ai t ++ l)}
  -> rewriteLeft (sym (coprod ao t [] k))
                 (rewriteRight (sym (coprod ai t [] l))
                               (permComp (permComp w (permId (sumArity ai t ++ l)))
                                         (permComp (permAddIdL (sumArity ai t) (permId l))
                                                   (swapAddIdR (sumArity ai t) [] l)))) =
     w
wr {ai} {t} _ l {w} = rewriteLeftIgnore $ rewriteRightIgnore $
  permCompCong5 Refl Refl Refl
    (permCompRightId w)
    (permCompCong5 Refl Refl Refl
      (permAddIdLPreserveId (sumArity ai t) l)
      (swapAddIdRNilRightNeutral (sumArity ai t) l)
    `trans` permCompRightId (permId (sumArity ai t ++ l)))
  `trans` permCompRightId w

assoc : {ai, ao : s -> List o} -> {t1, t2, t3 : List s} -> (k, l, m, n : List o)
     -> {w1 : Perm (sumArity ao t1 ++ k) (sumArity ai t1 ++ l)}
     -> {w2 : Perm (sumArity ao t2 ++ l) (sumArity ai t2 ++ m)}
     -> {w3 : Perm (sumArity ao t3 ++ m) (sumArity ai t3 ++ n)}
     -> rewriteLeft (sym (coprod ao t1 (t2 ++ t3) k))
                    (rewriteRight (sym (coprod ai t1 (t2 ++ t3) n))
                                  (permComp (permComp (permAddIdL (sumArity ao (t2 ++ t3)) w1) (swapAddIdR (sumArity ao (t2 ++ t3)) (sumArity ai t1) l))
                                            (permComp (permAddIdL (sumArity ai t1)
                                                                  (rewriteLeft (sym (coprod ao t2 t3 l))
                                                                               (rewriteRight (sym (coprod ai t2 t3 n))
                                                                                             (permComp (permComp (permAddIdL (sumArity ao t3) w2)
                                                                                                                 (swapAddIdR (sumArity ao t3) (sumArity ai t2) m))
                                                                                                       (permComp (permAddIdL (sumArity ai t2) w3)
                                                                                                                 (swapAddIdR (sumArity ai t2) (sumArity ai t3) n))))))
                                                      (swapAddIdR (sumArity ai t1) (sumArity ai (t2 ++ t3)) n)))) =
        rewriteLeft (sym (coprod ao (t1 ++ t2) t3 k))
                    (rewriteRight (sym (coprod ai (t1 ++ t2) t3 n))
                                  (permComp (permComp (permAddIdL (sumArity ao t3)
                                                                  (rewriteLeft (sym (coprod ao t1 t2 k))
                                                                               (rewriteRight (sym (coprod ai t1 t2 m))
                                                                                             (permComp (permComp (permAddIdL (sumArity ao t2) w1)
                                                                                                                 (swapAddIdR (sumArity ao t2) (sumArity ai t1) l))
                                                                                                       (permComp (permAddIdL (sumArity ai t1) w2)
                                                                                                                 (swapAddIdR (sumArity ai t1) (sumArity ai t2) m))))))
                                                      (swapAddIdR (sumArity ao t3) (sumArity ai (t1 ++ t2)) m))
                                            (permComp (permAddIdL (sumArity ai (t1 ++ t2)) w3) (swapAddIdR (sumArity ai (t1 ++ t2)) (sumArity ai t3) n))))
assoc {ai} {ao} {t1} {t2} {t3} k l m n {w1} {w2} {w3} =
  trans (rewriteLeftIgnore $ rewriteRightIgnore step1)
        (trans (permAssoc _ _ _)
               (sym $ rewriteLeftIgnore $ rewriteRightIgnore step2))
  where
    -- b -------------\ /- e --
    --     +---+       X     --
    -- c --|   |-- e -/ \- b --
    --     | w |             --
    -- d --|   |-- f ----- f --
    --     +---+             --
    compPart : (b : List o) -> (w : Perm (c ++ d) (e ++ f)) -> Perm (b ++ c ++ d) (e ++ b ++ f)
    compPart b {e} {f} w = permComp (permAddIdL b w) (swapAddIdR b e f)

    -- a ---------------\ /- e --
    --                   X
    -- b -------------\ /-\- a --
    --     +---+       X       --
    -- c --|   |-- e -/ \--- b --
    --     | w |               --
    -- d --|   |-- f ------- f --
    --     +---+               --
    compPart2 : (a, b : List o) -> {c, d, e, f : List o} -> (w : Perm (c ++ d) (e ++ f)) -> Perm (a ++ b ++ c ++ d) (e ++ a ++ b ++ f)
    compPart2 a b {c} {d} {e} {f} w = compPart a (compPart b w)

    compPartCong2 : (a = b) -> (v = w) -> compPart a v = compPart b w
    compPartCong2 Refl Refl = Refl

    compPartDist : (a, b : List o) -> (w : Perm (c ++ d) (e ++ f)) -> compPart (a ++ b) w = compPart2 a b w
    compPartDist a b w {c} {d} {e} {f} =
      trans (permCompCong5 (sym $ appendAssociative a b (c ++ d))
                           (sym $ appendAssociative a b (e ++ f))
                           (cong $ sym $ appendAssociative a b f)
                           (permAddIdLAppend a b w)
                           (sym $ swapHexagonal2' a b e f))
            (trans (permAssoc _ _ _)
                   (permCompCong5 Refl Refl Refl (sym $ permAddIdLCompDist a _ _) Refl))

    step1a : compPart (sumArity ao (t2 ++ t3)) w1 = compPart2 (sumArity ao t3) (sumArity ao t2) w1
    step1a = compPartCong2 (sym $ coprod' ao t2 t3) Refl `trans` compPartDist (sumArity ao t3) (sumArity ao t2) w1

    step2a : compPart (sumArity ai (t1 ++ t2)) w3 = compPart2 (sumArity ai t2) (sumArity ai t1) w3
    step2a = compPartCong2 (sym $ coprod' ai t1 t2) Refl `trans` compPartDist (sumArity ai t2) (sumArity ai t1) w3

    step1b1 : permComp (permAddIdL (sumArity ai t1) (rewriteLeft (sym (coprod ao t2 t3 l))
                                                                 (rewriteRight (sym (coprod ai t2 t3 n))
                                                                              (permComp (permComp (permAddIdL (sumArity ao t3) w2) (swapAddIdR (sumArity ao t3) (sumArity ai t2) m))
                                                                                        (permComp (permAddIdL (sumArity ai t2) w3) (swapAddIdR (sumArity ai t2) (sumArity ai t3) n))))))
                       (swapAddIdR (sumArity ai t1) (sumArity ai (t2 ++ t3)) n) =
              permComp (permAddIdL (sumArity ai t1)
                                    (permComp (permComp (permAddIdL (sumArity ao t3) w2) (swapAddIdR (sumArity ao t3) (sumArity ai t2) m))
                                              (permComp (permAddIdL (sumArity ai t2) w3) (swapAddIdR (sumArity ai t2) (sumArity ai t3) n))))
                       (permComp (swapAddIdR (sumArity ai t1) (sumArity ai t3) (sumArity ai t2 ++ n))
                                 (permAddIdL (sumArity ai t3) (swapAddIdR (sumArity ai t1) (sumArity ai t2) n)))
    step1b1 = permCompCong5 (cong {f=\z=>sumArity ai t1 ++ z} $ sym $ coprod ao t2 t3 l)
                            (cong {f=\z=>sumArity ai t1 ++ z} $ sym $ coprod ai t2 t3 n)
                            (sym $ coprod ai t2 t3 (sumArity ai t1 ++ n))
                            (permAddIdLCong4 Refl
                                             (sym $ coprod ao t2 t3 l)
                                             (sym $ coprod ai t2 t3 n)
                                             (rewriteLeftIgnore $ rewriteRightIgnore Refl))
                            (trans (swapAddIdRCong3 Refl (sym $ coprod' ai t2 t3) Refl)
                                   (sym $ swapHexagonal1' (sumArity ai t1) (sumArity ai t3) (sumArity ai t2) n))

    -- 1 ---------\/----- 3 --    -- 1 --\/--------\/-- 3 --
    -- 2 ------\/ /\-\/-- 2 --    -- 2 --/\-----\/-/\-- 2 --
    -- 3 --|w|-/\----/\-- 1 --    -- 3 -----|w|-/\----- 1 --
    -- m --|3|----------- n --    -- m -----|3|-------- n --
    step1b2 : permComp (permAddIdL (sumArity ai t1) (permComp (permAddIdL (sumArity ai t2) w3) (swapAddIdR (sumArity ai t2) (sumArity ai t3) n)))
                       (permComp (swapAddIdR (sumArity ai t1) (sumArity ai t3) (sumArity ai t2 ++ n))
                                 (permAddIdL (sumArity ai t3) (swapAddIdR (sumArity ai t1) (sumArity ai t2) n))) =
              permComp (swapAddIdR (sumArity ai t1) (sumArity ai t2) (sumArity ao t3 ++ m))
                       (permComp (permAddIdL (sumArity ai t2) (permComp (permAddIdL (sumArity ai t1) w3) (swapAddIdR (sumArity ai t1) (sumArity ai t3) n)))
                                 (swapAddIdR (sumArity ai t2) (sumArity ai t3) (sumArity ai t1 ++ n)))

    step1b : compPart (sumArity ai t1)
                      (rewriteLeft (sym (coprod ao t2 t3 l))
                                   (rewriteRight (sym (coprod ai t2 t3 n))
                                                 (permComp (compPart (sumArity ao t3) w2)
                                                           (compPart (sumArity ai t2) w3))))
           = permComp (compPart2 (sumArity ai t1) (sumArity ao t3) w2)
                      (compPart2 (sumArity ai t2) (sumArity ai t1) w3)
    step1b =
      trans step1b1
            (trans (permCompCong5 Refl Refl Refl (permAddIdLCompDist _ _ _) Refl)
                   (trans (sym (permAssoc _ _ _))
                          (trans (permCompCong5 Refl Refl Refl Refl step1b2)
                                 (permAssoc _ _ _))))

    step2b : compPart (sumArity ao t3)
                      (rewriteLeft (sym (coprod ao t1 t2 k))
                                   (rewriteRight (sym (coprod ai t1 t2 m))
                                                 (permComp (compPart (sumArity ao t2) w1)
                                                           (compPart (sumArity ai t1) w2))))
           = permComp (compPart2 (sumArity ao t3) (sumArity ao t2) w1)
                      (compPart2 (sumArity ai t1) (sumArity ao t3) w2)

    step1 : permComp (compPart (sumArity ao (t2 ++ t3)) w1)
                     (compPart (sumArity ai t1)
                               (rewriteLeft (sym (coprod ao t2 t3 l))
                                            (rewriteRight (sym (coprod ai t2 t3 n))
                                                          (permComp (compPart (sumArity ao t3) w2)
                                                                    (compPart (sumArity ai t2) w3)))))
          = permComp (compPart2 (sumArity ao t3) (sumArity ao t2) w1)
                     (permComp (compPart2 (sumArity ai t1) (sumArity ao t3) w2)
                               (compPart2 (sumArity ai t2) (sumArity ai t1) w3))
    step1 = permCompCong5 (sym $ coprod ao t2 t3 (sumArity ao t1 ++ k))
                          (cong $ sym $ coprod ao t2 t3 l)
                          (sym $ coprod ai t2 t3 (sumArity ai t1 ++ n))
                          step1a
                          step1b

    step2 : permComp (compPart (sumArity ao t3)
                               (rewriteLeft (sym (coprod ao t1 t2 k))
                                            (rewriteRight (sym (coprod ai t1 t2 m))
                                                          (permComp (compPart (sumArity ao t2) w1)
                                                                    (compPart (sumArity ai t1) w2)))))
                     (compPart (sumArity ai (t1 ++ t2)) w3)
          = permComp (permComp (compPart2 (sumArity ao t3) (sumArity ao t2) w1)
                               (compPart2 (sumArity ai t1) (sumArity ao t3) w2))
                     (compPart2 (sumArity ai t2) (sumArity ai t1) w3)
    step2 = permCompCong5 (cong $ sym $ coprod ao t1 t2 k)
                          (sym $ coprod ai t1 t2 (sumArity ao t3 ++ m))
                          (cong $ sym $ coprod ai t1 t2 n)
                          step2b
                          step2a

hgLeftId : {s : Type} -> {ai, ao : s -> List o} -> (k, l : List o)
        -> (hg : Hypergraph s ai ao k l) -> compose (identity k) hg = hg
hgLeftId k l (MkHypergraph t w) = hgCong2 Refl (wl k l)

hgRightId : {s : Type} -> {ai, ao : s -> List o} -> (k, l : List o)
         -> (hg : Hypergraph s ai ao k l) -> compose hg (identity l) = hg
hgRightId k l (MkHypergraph t w) = hgCong2 (appendNilRightNeutral t) (wr k l)

hgAssoc : {s : Type} -> {ai, ao : s -> List o} -> (k, l, m, n : List o)
       -> (hg1 : Hypergraph s ai ao k l) -> (hg2 : Hypergraph s ai ao l m) -> (hg3 : Hypergraph s ai ao m n)
       -> compose hg1 (compose hg2 hg3) = compose (compose hg1 hg2) hg3
hgAssoc k l m n (MkHypergraph t1 w1) (MkHypergraph t2 w2) (MkHypergraph t3 w3) = hgCong2 (appendAssociative t1 t2 t3) (assoc k l m n)

hypergraphCat : (sigma : Type) -> (arityIn : sigma -> List o) -> (arityOut : sigma -> List o) -> Category
hypergraphCat {o} sigma arityIn arityOut = MkCategory
  (List o)
  (Hypergraph sigma arityIn arityOut)
  identity
  (\_,_,_ => compose)
  hgLeftId
  hgRightId
  hgAssoc
