module Cartographer.Hypergraph

import Data.List

import Permutations.SwapDown
import Permutations.Permutations
import Permutations.PermutationsCategory

%access public export
%default total

-- equivalent to concatMap, but `concatMap a t` is expanded in holes to this ugly thing:
-- Prelude.List.List implementation of Prelude.Foldable.Foldable, method foldr (\x, meth => a x ++ meth) [] t
sumArity : (a : sigma -> List o) -> List sigma -> List o
sumArity _ Nil = []
sumArity a (s :: ss) = sumArity a ss ++ a s

coprod
   : (a : s -> List o) -> (t1, t2 : List s) -> (r : List o)
  -> sumArity a t2 ++ sumArity a t1 ++ r = sumArity a (t1 ++ t2) ++ r
coprod a Nil     _  r = Refl
coprod a (s::t1) t2 r = trans (cong $ sym $ appendAssociative _ _ _) (trans (coprod a t1 t2 (a s ++ r)) (appendAssociative _ _ _))

coprod'
   : (a : s -> List o) -> (t1, t2 : List s)
  -> sumArity a t2 ++ sumArity a t1 = sumArity a (t1 ++ t2)
coprod' a Nil     _  = appendNilRightNeutral _
coprod' a (s::t1) t2 = appendAssociative _ _ _ `trans` cong {f=\z=>z++a s} (coprod' a t1 t2)

swArity : (ar : sigma -> List o) -> {s1, s2 : List sigma} -> SwapDown s1 s2 -> Perm (sumArity ar s1) (sumArity ar s2)
swArity ar (HereS {a} {as}) = permId (sumArity ar as ++ ar a)
swArity ar (ThereS {a} {b} {as} {bs} sw) = rewriteLeft (sym $ appendAssociative (sumArity ar as) (ar b) (ar a)) $
  permComp (permAddIdL (sumArity ar as) (swap (ar b) (ar a)))
           (rewriteLeft (appendAssociative _ _ _) $ permAdd (swArity ar sw) (permId (ar b)))

permArity : (ar : sigma -> List o) -> {s1, s2 : List sigma} -> Perm s1 s2 -> Perm (sumArity ar s1) (sumArity ar s2)
permArity _   Nil = Nil
permArity ar (Ins {a} {xs=as} {ys} p s) = permComp (permArity ar p `permAdd` permId (ar a)) (swArity ar s)

record Hypergraph (sigma : Type) (arityIn : sigma -> List o) (arityOut : sigma -> List o) (k : List o) (m : List o) where
  constructor MkHypergraph
  -- HyperEdges
  Typ : List sigma
  wiring : Perm (sumArity arityOut Typ ++ k) (sumArity arityIn Typ ++ m)

postulate
hypergraphEq :
     {s : Type}
  -> {ai, ao : s -> List o}
  -> {k, m : List o}
  -> {hg1, hg2 : Hypergraph s ai ao k m}
  -> (p : Perm (Typ hg1) (Typ hg2))
  -> (wiring hg1 `permComp` (permArity ai p `permAdd` permId m) = (permArity ao p `permAdd` permId k) `permComp` wiring hg2)
  -> hg1 = hg2

singleton : {s : Type} -> {ai, ao : s -> List o} -> (edge : s) -> Hypergraph s ai ao (ai edge) (ao edge)
singleton edge = MkHypergraph [edge] (swap (ao edge) (ai edge))

permutation : {s : Type} -> {ai, ao : s -> List o} -> Perm k m -> Hypergraph s ai ao k m
permutation p = MkHypergraph [] p

identity : {s : Type} -> {ai, ao : s -> List o} -> (n : List o) -> Hypergraph s ai ao n n
identity n = permutation (permId n)

zero : {s : Type} -> {ai, ao : s -> List o} -> Hypergraph s ai ao [] []
zero = identity []

compose : (g1 : Hypergraph s ai ao k m) -> (g2 : Hypergraph s ai ao m n) -> Hypergraph s ai ao k n
compose (MkHypergraph t1 c1) (MkHypergraph t2 c2) = MkHypergraph (t1 ++ t2) perm
  where
    helper : Perm (o1 ++ k) (i1 ++ m) -> Perm (o2 ++ m) (i2 ++ n) -> o2 ++ o1 ++ k = o12 ++ k -> i2 ++ i1 ++ n = i12 ++ n -> Perm (o12 ++ k) (i12 ++ n)
    helper {o1} {o2} {i1} {i2} c1 c2 oEq iEq =
      rewriteLeft (sym oEq) $
      rewriteRight (sym iEq) $
        permComp (permComp (o2 `permAddIdL` c1) (swapAddIdR o2 i1 m))
                 (permComp (i1 `permAddIdL` c2) (swapAddIdR i1 i2 n))

    perm : Perm (sumArity ao (t1 ++ t2) ++ k) (sumArity ai (t1 ++ t2) ++ n)
    perm = helper c1 c2 (coprod ao t1 t2 k) (coprod ai t1 t2 n)

add : Hypergraph s ai ao k l -> Hypergraph s ai ao m n -> Hypergraph s ai ao (k ++ m) (l ++ n)
add {k} {l} {m} {n} (MkHypergraph t1 c1) (MkHypergraph t2 c2) = MkHypergraph (t1 ++ t2) perm
  where
    helper : Perm (o1 ++ k) (i1 ++ l) -> Perm (o2 ++ m) (i2 ++ n) -> o2 ++ o1 ++ k ++ m = o12 ++ k ++ m -> i2 ++ i1 ++ l ++ n = i12 ++ l ++ n -> Perm (o12 ++ k ++ m) (i12 ++ l ++ n)
    helper {o1} {o2} {i1} {i2} c1 c2 oEq iEq =
      rewriteLeft (sym oEq `trans` cong (appendAssociative o1 k m)) $
      rewriteRight (sym iEq `trans` cong (appendAssociative i1 l n)) $
        permComp (swapAddIdR o2 (o1 ++ k) m)
                 (permComp (c1 `permAdd` c2)
                           (swapAddIdR (i1 ++ l) i2 n))

    perm : Perm (sumArity ao (t1 ++ t2) ++ (k ++ m)) (sumArity ai (t1 ++ t2) ++ (l ++ n))
    perm = helper c1 c2 (coprod ao t1 t2 (k ++ m)) (coprod ai t1 t2 (l ++ n))
