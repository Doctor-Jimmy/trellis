import Tablet.IncSeq
import Tablet.ProperPrefixSet

-- [TABLET NODE: FinitePrefixExtension]
theorem FinitePrefixExtension (s : Finset Nat) :
    ∃ x : IncSeq, ProperPrefixSet s (Set.range (x : Nat → Nat)) := by
-- BODY
  classical
  by_cases hs : s = ∅
  · subst s
    let x : IncSeq := OrderEmbedding.id Nat
    refine ⟨x, 0, ?_, ?_⟩
    · simpa [x] using (Set.mem_range_self 0 : (OrderEmbedding.id Nat : Nat → Nat) 0 ∈
        Set.range (OrderEmbedding.id Nat : Nat → Nat))
    · intro k
      simp [x]
  · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    let m : Nat := s.max' hsne
    let Y : Set Nat := (↑s : Set Nat) ∪ Set.Ioi m
    have hYinf : Y.Infinite := by
      apply Set.infinite_of_injective_forall_mem (f := fun n : Nat => m + 1 + n)
      · intro a b hab
        exact Nat.add_left_cancel hab
      · intro n
        change m + 1 + n ∈ (↑s : Set Nat) ∪ Set.Ioi m
        rw [Set.mem_union]
        right
        exact Set.mem_Ioi.mpr (by omega)
    letI : Infinite Y := hYinf.to_subtype
    let x : IncSeq := Nat.orderEmbeddingOfSet Y
    refine ⟨x, m + 1, ?_, ?_⟩
    · rw [show (x : Nat → Nat) = Nat.orderEmbeddingOfSet Y by rfl]
      rw [Nat.orderEmbeddingOfSet_range Y]
      change m + 1 ∈ (↑s : Set Nat) ∪ Set.Ioi m
      rw [Set.mem_union]
      right
      exact Set.mem_Ioi.mpr (by omega)
    · intro k
      rw [show (x : Nat → Nat) = Nat.orderEmbeddingOfSet Y by rfl]
      rw [Nat.orderEmbeddingOfSet_range Y]
      change k ∈ s ↔ k ∈ (↑s : Set Nat) ∪ Set.Ioi m ∧ k < m + 1
      constructor
      · intro hk
        refine ⟨by
          rw [Set.mem_union]
          exact Or.inl (Finset.mem_coe.mpr hk), ?_⟩
        exact Nat.lt_succ_of_le (Finset.le_max' s k hk)
      · intro hk
        rw [Set.mem_union] at hk
        rcases hk.1 with hks | hkm
        · exact Finset.mem_coe.mp hks
        · exfalso
          rw [Set.mem_Ioi] at hkm
          omega
