module Permutations.SwapDown

%access public export
%default total

data SwapDown : List t -> List t -> Type where
  HereS  : SwapDown (a::as) (a::as)
  ThereS : SwapDown (a::as) bs -> SwapDown (a::b::as) (b::bs)

Uninhabited (SwapDown (x::xs) []) where
  uninhabited  HereS     impossible
  uninhabited (ThereS _) impossible

congHereS : (as1 = as2) -> (HereS {a} {as=as1} = HereS {a} {as=as2})
congHereS Refl = Refl

congThereS : {t : Type} -> {b : t} -> (as1 = as2) -> (bs1 = bs2)
          -> {sw1 : SwapDown (a::as1) bs1} -> {sw2 : SwapDown (a::as2) bs2}
          -> (sw1 = sw2) -> ThereS {a} {b} {as=as1} {bs=bs1} sw1 = ThereS {a} {b} {as=as2} {bs=bs2} sw2
congThereS Refl Refl Refl = Refl

swapDown : (l : List t) -> SwapDown (a :: l ++ r) (l ++ a :: r)
swapDown []      = HereS
swapDown (l::ls) = ThereS (swapDown ls)

appended : (s : List t) -> SwapDown as bs -> SwapDown (as ++ s) (bs ++ s)
appended _  HereS      = HereS
appended s (ThereS sw) = ThereS (appended s sw)

appendedNilNeutral : (sw: SwapDown as bs) -> appended [] sw = sw
appendedNilNeutral (HereS {as}) = congHereS (appendNilRightNeutral as)
appendedNilNeutral (ThereS {as} {bs} sw) =
  congThereS (appendNilRightNeutral as) (appendNilRightNeutral bs) (appendedNilNeutral sw)

appendedAppendDistr : (xs, ys : List t) -> (sw: SwapDown as bs) -> appended (xs ++ ys) sw = appended ys (appended xs sw)
appendedAppendDistr xs ys (HereS {as}) = congHereS (appendAssociative as xs ys)
appendedAppendDistr xs ys (ThereS {as} {bs} sw) =
  congThereS (appendAssociative as xs ys) (appendAssociative bs xs ys) (appendedAppendDistr xs ys sw)

swapDownAppendedNeutral : (as, bs, cs : List t) -> {a:t} -> swapDown as {a} {r=bs++cs} = appended cs (swapDown as {a} {r=bs})
swapDownAppendedNeutral [] bs cs = congHereS Refl
swapDownAppendedNeutral (a::as) bs cs = congThereS (appendAssociative as bs cs) (appendAssociative as (_::bs) cs) (swapDownAppendedNeutral as bs cs)

data SwapDown2 : t -> t -> List t -> List t -> Type where
  SW2 : SwapDown (b :: xs) ys -> SwapDown (a :: ys) zs -> SwapDown2 a b xs zs

swComb : SwapDown (a :: xs) ys -> SwapDown (b :: ys) zs -> SwapDown2 a b xs zs
swComb         axy   HereS       = SW2 HereS (ThereS axy)
swComb  HereS       (ThereS bxy) = SW2 bxy    HereS
swComb (ThereS axy) (ThereS byz) = let SW2 bxy ayz = swComb axy byz in SW2 (ThereS bxy) (ThereS ayz)
