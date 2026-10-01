import Tablet.FrontPrefix

-- [TABLET NODE: FrontPrefixExists]
theorem FrontPrefixExists (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (x : IncSeq)
    (hx : Set.range (x : Nat → Nat) ⊆ X) :
    ∃ s : Finset Nat, FrontPrefix F s x := by
-- BODY
  sorry
