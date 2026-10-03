import Tablet.Preamble

-- [TABLET NODE: BooleanInfinitePigeonhole]
theorem BooleanInfinitePigeonhole (b : Nat → Bool) :
    ∃ c : Bool, Set.Infinite {n | b n = c} := by
-- BODY
  by_cases ht : Set.Infinite {n | b n = true}
  · exact ⟨true, ht⟩
  · by_cases hf : Set.Infinite {n | b n = false}
    · exact ⟨false, hf⟩
    · exfalso
      have hft : ({n | b n = true} : Set Nat).Finite := Set.not_infinite.mp ht
      have hff : ({n | b n = false} : Set Nat).Finite := Set.not_infinite.mp hf
      have hunion : ({n | b n = true} ∪ {n | b n = false} : Set Nat) = Set.univ := by
        ext n
        cases hb : b n <;> simp [hb]
      have hfin : (Set.univ : Set Nat).Finite := by
        rw [← hunion]
        exact hft.union hff
      exact (Set.not_infinite.mpr hfin) Set.infinite_univ
