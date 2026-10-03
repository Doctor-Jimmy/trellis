import Tablet.BadPairSequence
import Tablet.SetDomination

-- [TABLET NODE: PowerWqoBadPairSequence]
theorem PowerWqoBadPairSequence {Q : Type} (r : Q → Q → Prop)
    [IsPreorder Q r] :
    ¬ WellQuasiOrdered (SetDomination r) ↔
      ∃ f : IncreasingPair → Q, BadPairSequence r f := by
-- BODY
  constructor
  · intro h
    unfold WellQuasiOrdered at h
    push Not at h
    obtain ⟨P, hP⟩ := h
    have hnot : ∀ m n : Nat, m < n →
        ∃ p ∈ P m, ∀ q ∈ P n, ¬ r p q := by
      intro m n hmn
      have hmn' : ¬ SetDomination r (P m) (P n) := hP m n hmn
      unfold SetDomination at hmn'
      push Not at hmn'
      exact hmn'
    classical
    let f : IncreasingPair → Q := fun ij =>
      Classical.choose (hnot ij.first ij.second ij.increasing)
    have hf : ∀ ij : IncreasingPair, f ij ∈ P ij.first ∧
        ∀ q ∈ P ij.second, ¬ r (f ij) q := by
      intro ij
      exact Classical.choose_spec (hnot ij.first ij.second ij.increasing)
    refine ⟨f, ?_⟩
    intro m n l hmn hnl hrel
    have hfirst := (hf ⟨m, n, hmn⟩).2
        (f ⟨n, l, hnl⟩) ((hf ⟨n, l, hnl⟩).1)
    exact hfirst hrel
  · rintro ⟨f, hf⟩
    unfold WellQuasiOrdered
    intro h
    let P : Nat → Set Q := fun m =>
      {q | ∃ (n : Nat) (hmn : m < n), q = f ⟨m, n, hmn⟩}
    obtain ⟨m, n, hmn, hdom⟩ := h P
    have hmem : f ⟨m, n, hmn⟩ ∈ P m := by
      exact ⟨n, hmn, rfl⟩
    obtain ⟨q, hq, hrel⟩ := hdom _ hmem
    obtain ⟨l, hnl, hqeq⟩ := hq
    subst q
    exact (hf m n l hmn hnl) hrel
