import Tablet.Front
import Tablet.Ray

-- [TABLET NODE: FrontRayPrefixFree]
theorem FrontRayPrefixFree (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (n : Nat) {s t : Finset Nat}
    (hs : s ∈ Ray F n) (ht : t ∈ Ray F n)
    (hst : InitialSegment s t) : s = t := by
-- BODY
  have hinsert : InitialSegment (insert n s) (insert n t) := by
    rcases hst with rfl | ⟨m, hm, hst⟩
    · exact Or.inl rfl
    · right
      refine ⟨m, Finset.mem_insert_of_mem hm, ?_⟩
      ext k
      have hnm : n < m := ht.1 m hm
      by_cases hkn : k = n
      · subst k
        simp [hnm]
      · simp only [Finset.mem_insert, hkn, false_or, Finset.mem_filter]
        simpa [hst]
  have hins : insert n s = insert n t := hF.prefix_free hs.2 ht.2 hinsert
  ext k
  by_cases hkn : k = n
  · subst k
    have hns : n ∉ s := by
      intro hns
      exact Nat.lt_irrefl n (hs.1 n hns)
    have hnt : n ∉ t := by
      intro hnt
      exact Nat.lt_irrefl n (ht.1 n hnt)
    simp [hns, hnt]
  · simpa [Finset.mem_insert, hkn] using congrArg (fun q => k ∈ q) hins
