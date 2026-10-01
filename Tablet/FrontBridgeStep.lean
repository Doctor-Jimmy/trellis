import Tablet.FrontBridge
import Tablet.FrontTreeOrderedExtension

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
  sorry
