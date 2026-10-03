import Tablet.FrontBridge
import Tablet.FrontTreeOrderedExtension
import Tablet.FrontBridgeTailInsert
import Tablet.InitialSegmentInsert
import Tablet.FrontBridgeRightResponse

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
    rcases FrontBridgeRightResponse F ht_tree ht_ne hu_ne (ht_init) (ht_tail)
        (hs_init hsF) hright with
      ⟨ht'_tree, ht'_ne', hu'_ne, ⟨q, hqu, hu'_eq⟩, hs'_init,
        ht'_init, ht'_tail⟩
    refine ⟨?_, hs_tree, hfinal_eq, hfinal_ext⟩
    refine ⟨hs_tree, ht'_tree, ht'_ne', hu'_ne, ?_, ?_, ?_, ?_⟩
    · intro _
      exact hs'_init
    · intro hsnot
      exact (hsnot hsF).elim
    · exact ht'_init
    · exact ht'_tail
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
    rcases FrontBridgeRightResponse F ht_tree ht_ne hu_ne (ht_init) (ht_tail)
        (Or.inl rfl) hright with
      ⟨ht'_tree, ht'_ne', hu'_ne, ⟨q, hqu, hu'_eq⟩, hu'_init',
        ht'_init, ht'_tail⟩
    refine ⟨?_, hu_tree, hfinal_eq, hfinal_ext⟩
    refine ⟨hu_tree, ht'_tree, ht'_ne', hu'_ne, ?_, ?_, ?_, ?_⟩
    · intro _
      exact hu'_init'
    · intro hu_notF
      exact ⟨q, hleft_proper q hqu, hu'_eq,
        by rw [hu'_eq]; exact hleft_tree q hqu hu_notF⟩
    · exact ht'_init
    · exact ht'_tail
