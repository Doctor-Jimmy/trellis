import Tablet.FrontPrefix

-- [TABLET NODE: FrontPrefixExists]
theorem FrontPrefixExists (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (x : IncSeq)
    (hx : Set.range (x : Nat → Nat) ⊆ X) :
    ∃ s : Finset Nat, FrontPrefix F s x := by
-- BODY
  have hR : (Set.range (x : Nat → Nat)).Infinite :=
    Set.infinite_range_of_injective x.injective
  obtain ⟨s, hsF, hsP⟩ := hF.dense (Set.range (x : Nat → Nat)) hx hR
  exact ⟨s, hsF, hsP⟩
