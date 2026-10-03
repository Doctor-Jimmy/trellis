import Tablet.InitialSegment

-- [TABLET NODE: DecidingFrontInitialTrans]
theorem DecidingFrontInitialTrans {a b c : Finset Nat}
    (hab : InitialSegment a b) (hbc : InitialSegment b c) :
    InitialSegment a c := by
-- BODY
  rcases hab with rfl | ⟨n, hn, ha⟩
  · exact hbc
  rcases hbc with rfl | ⟨m, hm, hb⟩
  · exact Or.inr ⟨n, hn, ha⟩
  · have hn' : n ∈ c.filter (fun k => k < m) := hb ▸ hn
    have hnm : n < m := (Finset.mem_filter.mp hn').2
    have hnc : n ∈ c := (Finset.mem_filter.mp hn').1
    refine Or.inr ⟨n, hnc, ?_⟩
    rw [ha, hb]
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk, hkm⟩, hkn⟩
      exact ⟨hk, hkn⟩
    · rintro ⟨hk, hkn⟩
      exact ⟨⟨hk, lt_trans hkn hnm⟩, hkn⟩
