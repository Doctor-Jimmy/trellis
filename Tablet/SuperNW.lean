import Tablet.NashWilliams
import Tablet.SuperSequence

-- [TABLET NODE: SuperNW]
theorem SuperNW (E : Type) [Fintype E] (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (f : SuperSequence F X E) :
    ∃ F' : Set (Finset Nat), ∃ Y : Set Nat,
      ∃ hF' : Front F' Y, ∃ hsub : F' ⊆ F,
        ∃ c : E, ∀ s : F', f.value ⟨s.1, hsub s.2⟩ = c := by
-- BODY
  sorry
