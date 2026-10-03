import Tablet.FrontBridge
import Tablet.FrontTreeOrderedExtension
import Tablet.FrontBridgeTailInsert
import Tablet.InitialSegmentInsert

-- [TABLET NODE: FrontBridgeStep]
theorem FrontBridgeStep (F : Set (Finset Nat))
    (hF : Front F Set.univ) {s t u s' t' u' : Finset Nat}
    (hb : FrontBridge F s t u)
    (hleft : (s ∈ F ∧ s' = s) ∨ (s ∉ F ∧ s' = u))
    (hright :
      (t ∉ F ∧ t.Nonempty ∧ ProperInitialSegment t t' ∧
        t' ∈ PrefixTree F ∧
        ∃ n, t' = insert n t ∧ (∀ j, j ∈ u → j < n) ∧
          u' = insert n u) ∨
      (t ∈ F ∧ t' = t ∧
        ∃ k, (∀ j, j ∈ u → j < k) ∧ u' = insert k u)) :
    FrontBridge F s' t' u' ∧
      s' ∈ PrefixTree F ∧
      (s ∈ F → s' = s) ∧
      (s ∉ F → ∃ n, s' = insert n s ∧
        ProperInitialSegment s (insert n s)) := by
-- BODY
  classical
  rw [FrontBridge] at hb ⊢
  rcases hb with ⟨hs_tree, ht_tree, ht_ne, hu_ne, hs_init, hs_ext,
    ht_init, ht_tail⟩
  rcases hleft with hleft | hleft
  · rcases hleft with ⟨hsF, hs'_eq⟩
    subst s'
    have hfinal_eq : s ∈ F → s = s := fun _ => rfl
    have hfinal_ext : s ∉ F → ∃ n, s = insert n s ∧
        ProperInitialSegment s (insert n s) := by
      intro hsnot
      exact (hsnot hsF).elim
    rcases hright with hright | hright
    · rcases hright with ⟨htF, ht'_ne, ht'_init, ht'_tree, n, ht'_eq,
        hnu, hu'_eq⟩
      have htail_ins : FrontBridgeTail u' = insert n (FrontBridgeTail u) := by
        rw [hu'_eq]
        exact FrontBridgeTailInsert u hu_ne n hnu
      have ht'_tail : t' = FrontBridgeTail u' := by
        calc
          t' = insert n t := ht'_eq
          _ = insert n (FrontBridgeTail u) := by rw [ht_tail htF]
          _ = FrontBridgeTail u' := htail_ins.symm
      have hs'_init : InitialSegment s u' := by
        rw [hu'_eq]
        exact InitialSegmentInsert s u (hs_init hsF) n hnu
      have ht'_ne' : t'.Nonempty := by
        rcases ht_ne with ⟨j, hj⟩
        exact ⟨j, ht'_eq ▸ Finset.mem_insert_of_mem hj⟩
      refine ⟨?_, hs_tree, hfinal_eq, hfinal_ext⟩
      refine ⟨hs_tree, ht'_tree, ht'_ne', ?_, ?_, ?_, ?_, ?_⟩
      · rw [hu'_eq]
        rcases hu_ne with ⟨j, hj⟩
        exact ⟨j, Finset.mem_insert_of_mem hj⟩
      · intro _
        exact hs'_init
      · intro hsnot
        exact (hsnot hsF).elim
      · intro ht'F
        exact Or.inl ht'_tail
      · intro ht'not
        exact ht'_tail
    · rcases hright with ⟨htF, ht'_eq, k, hku, hu'_eq⟩
      have htail_ins : FrontBridgeTail u' = insert k (FrontBridgeTail u) := by
        rw [hu'_eq]
        exact FrontBridgeTailInsert u hu_ne k hku
      have htail_k_lt : ∀ j ∈ FrontBridgeTail u, j < k := by
        intro j hj
        exact hku j ((Finset.mem_filter.mp hj).1)
      have ht'_init : InitialSegment t' (FrontBridgeTail u') := by
        rw [htail_ins]
        rw [ht'_eq]
        exact InitialSegmentInsert t (FrontBridgeTail u) (ht_init htF) k
          htail_k_lt
      have hs'_init : InitialSegment s u' := by
        rw [hu'_eq]
        exact InitialSegmentInsert s u (hs_init hsF) k hku
      have ht'_tree : t' ∈ PrefixTree F := by rw [ht'_eq]; exact ht_tree
      have ht'_ne' : t'.Nonempty := by rw [ht'_eq]; exact ht_ne
      refine ⟨?_, hs_tree, hfinal_eq, hfinal_ext⟩
      refine ⟨hs_tree, ht'_tree, ht'_ne', ?_, ?_, ?_, ?_, ?_⟩
      · rw [hu'_eq]
        rcases hu_ne with ⟨j, hj⟩
        exact ⟨j, Finset.mem_insert_of_mem hj⟩
      · intro _
        exact hs'_init
      · intro hsnot
        exact (hsnot hsF).elim
      · intro ht'F
        exact ht'_init
      · intro ht'not
        exact (ht'not (by rw [ht'_eq]; exact htF)).elim
  · rcases hleft with ⟨hsnot, hs'_eq⟩
    subst s'
    obtain ⟨a, has, hua, hu_tree⟩ := hs_ext hsnot
    have hleft_proper : ∀ q, (∀ j ∈ u, j < q) →
        ProperInitialSegment u (insert q u) := by
      intro q hqu
      refine ⟨InitialSegmentInsert u u (Or.inl rfl) q hqu, ?_⟩
      intro heq
      have hq_u : q ∈ u := by rw [heq]; exact Finset.mem_insert_self q u
      exact (Nat.lt_irrefl q) (hqu q hq_u)
    have hleft_tree : ∀ q, (∀ j ∈ u, j < q) → u ∉ F →
        insert q u ∈ PrefixTree F := by
      intro q hqu huF
      exact FrontTreeOrderedExtension F hF u hu_tree huF q
        (hleft_proper q hqu)
    have hfinal_eq : s ∈ F → u = s := by
      intro hsF
      exact (hsnot hsF).elim
    have hfinal_ext : s ∉ F → ∃ n, u = insert n s ∧
        ProperInitialSegment s (insert n s) := by
      intro _
      exact ⟨a, hua, has⟩
    rcases hright with hright | hright
    · rcases hright with ⟨htF, ht'_ne, ht'_init, ht'_tree, n, ht'_eq,
        hnu, hu'_eq⟩
      have htail_ins : FrontBridgeTail u' = insert n (FrontBridgeTail u) := by
        rw [hu'_eq]
        exact FrontBridgeTailInsert u hu_ne n hnu
      have ht'_tail : t' = FrontBridgeTail u' := by
        calc
          t' = insert n t := ht'_eq
          _ = insert n (FrontBridgeTail u) := by rw [ht_tail htF]
          _ = FrontBridgeTail u' := htail_ins.symm
      have hleft_init' : InitialSegment u u' := by
        rw [hu'_eq]
        exact InitialSegmentInsert u u (Or.inl rfl) n hnu
      have hleft_proper' : ProperInitialSegment u u' := by
        rw [hu'_eq]
        exact hleft_proper n hnu
      have ht'_ne' : t'.Nonempty := by
        rcases ht_ne with ⟨j, hj⟩
        exact ⟨j, ht'_eq ▸ Finset.mem_insert_of_mem hj⟩
      refine ⟨?_, hu_tree, hfinal_eq, hfinal_ext⟩
      refine ⟨hu_tree, ht'_tree, ht'_ne', ?_, ?_, ?_, ?_, ?_⟩
      · rw [hu'_eq]
        rcases hu_ne with ⟨j, hj⟩
        exact ⟨j, Finset.mem_insert_of_mem hj⟩
      · intro _
        exact hleft_init'
      · intro hu_notF
        exact ⟨n, hleft_proper n hnu, hu'_eq,
          by rw [hu'_eq]; exact hleft_tree n hnu hu_notF⟩
      · intro ht'F
        exact Or.inl ht'_tail
      · intro ht'not
        exact ht'_tail
    · rcases hright with ⟨htF, ht'_eq, k, hku, hu'_eq⟩
      have htail_ins : FrontBridgeTail u' = insert k (FrontBridgeTail u) := by
        rw [hu'_eq]
        exact FrontBridgeTailInsert u hu_ne k hku
      have htail_k_lt : ∀ j ∈ FrontBridgeTail u, j < k := by
        intro j hj
        exact hku j ((Finset.mem_filter.mp hj).1)
      have ht'_init : InitialSegment t' (FrontBridgeTail u') := by
        rw [htail_ins]
        rw [ht'_eq]
        exact InitialSegmentInsert t (FrontBridgeTail u) (ht_init htF) k
          htail_k_lt
      have hleft_init' : InitialSegment u u' := by
        rw [hu'_eq]
        exact InitialSegmentInsert u u (Or.inl rfl) k hku
      have hleft_proper' : ProperInitialSegment u u' := by
        rw [hu'_eq]
        exact hleft_proper k hku
      have ht'_tree : t' ∈ PrefixTree F := by rw [ht'_eq]; exact ht_tree
      have ht'_ne' : t'.Nonempty := by rw [ht'_eq]; exact ht_ne
      refine ⟨?_, hu_tree, hfinal_eq, hfinal_ext⟩
      refine ⟨hu_tree, ht'_tree, ht'_ne', ?_, ?_, ?_, ?_, ?_⟩
      · rw [hu'_eq]
        rcases hu_ne with ⟨j, hj⟩
        exact ⟨j, Finset.mem_insert_of_mem hj⟩
      · intro _
        exact hleft_init'
      · intro hu_notF
        exact ⟨k, hleft_proper k hku, hu'_eq,
          by rw [hu'_eq]; exact hleft_tree k hku hu_notF⟩
      · intro ht'F
        exact ht'_init
      · intro ht'not
        exact (ht'not (by rw [ht'_eq]; exact htF)).elim
