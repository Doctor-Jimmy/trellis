import Tablet.InitialSegment

-- [TABLET NODE: InitialSegmentInsert]
theorem InitialSegmentInsert (v u : Finset Nat) (hvu : InitialSegment v u)
    (q : Nat) (hqu : ∀ j ∈ u, j < q) :
    InitialSegment v (insert q u) := by
-- BODY
  rcases hvu with hvu | ⟨n, hn, hv⟩
  · subst v
    right
    refine ⟨q, Finset.mem_insert_self q u, ?_⟩
    apply Finset.ext
    intro k
    constructor
    · intro hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_insert_of_mem hk, hqu k hk⟩
    · intro hk
      have hk' := Finset.mem_filter.mp hk
      rcases Finset.mem_insert.mp hk'.1 with hkq | hk_u
      · subst k
        exact False.elim (Nat.lt_irrefl q hk'.2)
      · exact hk_u
  · right
    rw [hv]
    refine ⟨n, Finset.mem_insert_of_mem hn, ?_⟩
    apply Finset.ext
    intro k
    constructor
    · intro hk
      have hk' := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_insert_of_mem hk'.1, hk'.2⟩
    · intro hk
      have hk' := Finset.mem_filter.mp hk
      rcases Finset.mem_insert.mp hk'.1 with hkq | hk
      · subst k
        exact False.elim ((Nat.lt_irrefl q) (hk'.2.trans (hqu n hn)))
      · exact Finset.mem_filter.mpr ⟨hk, hk'.2⟩
