import Tablet.FrontBridge
import Tablet.FrontBridgeTailInsert
import Tablet.InitialSegmentInsert

-- [TABLET NODE: FrontBridgeRightResponse]
theorem FrontBridgeRightResponse (F : Set (Finset Nat))
    {t u t' u' x : Finset Nat}
    (ht_tree : t ∈ PrefixTree F) (ht_ne : t.Nonempty) (hu_ne : u.Nonempty)
    (ht_init : t ∈ F → InitialSegment t (FrontBridgeTail u))
    (ht_tail : t ∉ F → t = FrontBridgeTail u)
    (hx_init : InitialSegment x u)
    (hright :
      (t ∉ F ∧ t.Nonempty ∧ ProperInitialSegment t t' ∧
        t' ∈ PrefixTree F ∧
        ∃ n, t' = insert n t ∧ (∀ j, j ∈ u → j < n) ∧
          u' = insert n u) ∨
      (t ∈ F ∧ t' = t ∧
        ∃ k, (∀ j, j ∈ u → j < k) ∧ u' = insert k u)) :
    t' ∈ PrefixTree F ∧
      t'.Nonempty ∧
      u'.Nonempty ∧
      (∃ q, (∀ j, j ∈ u → j < q) ∧ u' = insert q u) ∧
      InitialSegment x u' ∧
      (t' ∈ F → InitialSegment t' (FrontBridgeTail u')) ∧
      (t' ∉ F → t' = FrontBridgeTail u') := by
-- BODY
  classical
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
    have hu'_ne : u'.Nonempty := by
      rw [hu'_eq]
      rcases hu_ne with ⟨j, hj⟩
      exact ⟨j, Finset.mem_insert_of_mem hj⟩
    have ht'_ne' : t'.Nonempty := by
      rcases ht'_ne with ⟨j, hj⟩
      exact ⟨j, ht'_eq ▸ Finset.mem_insert_of_mem hj⟩
    have hx_init' : InitialSegment x u' := by
      rw [hu'_eq]
      exact InitialSegmentInsert x u hx_init n hnu
    refine ⟨ht'_tree, ht'_ne', hu'_ne, ⟨n, hnu, hu'_eq⟩, hx_init', ?_, ?_⟩
    · intro ht'F
      exact Or.inl ht'_tail
    · intro _
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
    have hx_init' : InitialSegment x u' := by
      rw [hu'_eq]
      exact InitialSegmentInsert x u hx_init k hku
    have ht'_tree : t' ∈ PrefixTree F := by
      rw [ht'_eq]
      exact ht_tree
    have ht'_ne : t'.Nonempty := by
      rw [ht'_eq]
      exact ht_ne
    have hu'_ne : u'.Nonempty := by
      rw [hu'_eq]
      rcases hu_ne with ⟨j, hj⟩
      exact ⟨j, Finset.mem_insert_of_mem hj⟩
    refine ⟨ht'_tree, ht'_ne, hu'_ne, ⟨k, hku, hu'_eq⟩, hx_init', ?_, ?_⟩
    · intro _
      exact ht'_init
    · intro ht'not
      exact (ht'not (by rw [ht'_eq]; exact htF)).elim
