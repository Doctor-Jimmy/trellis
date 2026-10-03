import Tablet.IncSeqId
import Tablet.IncSeqPointwiseLe

-- [TABLET NODE: FirstMovedPoint]
theorem FirstMovedPoint (g : IncSeq) (hg : g ≠ IncSeqId) :
    ∃ k : Nat, k < g k ∧ ∀ j < k, g j = j := by
-- BODY
  have h_exists : ∃ n : Nat, g n ≠ n := by
    by_contra h
    apply hg
    apply DFunLike.ext g IncSeqId
    intro n
    have hn : g n = n := by
      by_contra hne
      exact h ⟨n, hne⟩
    simpa [IncSeqId] using hn
  let k : Nat := Nat.find h_exists
  have hk_moved : g k ≠ k := Nat.find_spec h_exists
  have hk_le : k ≤ g k := IncSeqPointwiseLe g k
  have hk_lt : k < g k := lt_of_le_of_ne hk_le (Ne.symm hk_moved)
  refine ⟨k, hk_lt, ?_⟩
  intro j hj
  have hj_not_moved : ¬ g j ≠ j := by
    intro hj_moved
    have hkj : k ≤ j := Nat.find_min' h_exists hj_moved
    exact (Nat.not_le_of_lt hj) hkj
  exact Classical.not_not.mp hj_not_moved
