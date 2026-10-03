import Tablet.FiniteShift
import Tablet.SuperSequence

universe u

-- [TABLET NODE: BadSuperSequence]
def BadSuperSequence {Q : Type u} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat}
    (f : SuperSequence F X Q) : Prop :=
-- BODY
  ∀ (s t : Finset Nat) (hs : s ∈ F) (ht : t ∈ F), FiniteShift s t →
    ¬ r (f.value ⟨s, hs⟩) (f.value ⟨t, ht⟩)
