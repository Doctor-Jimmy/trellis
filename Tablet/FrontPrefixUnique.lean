import Tablet.FrontPrefix

-- [TABLET NODE: FrontPrefixUnique]
theorem FrontPrefixUnique (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (x : IncSeq) {s t : Finset Nat}
    (hs : FrontPrefix F s x) (ht : FrontPrefix F t x) : s = t := by
-- BODY
  sorry
