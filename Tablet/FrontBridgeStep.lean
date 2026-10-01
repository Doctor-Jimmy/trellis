import Tablet.FrontBridgeLeftMove
import Tablet.FrontTreeOrderedExtension

-- [TABLET NODE: FrontBridgeStep]
theorem FrontBridgeStep (F : Set (Finset Nat))
    (hF : Front F Set.univ) {s t u s' t' u' : Finset Nat}
    (hb : FrontBridge F s t u)
    (hleft : (s ∈ F ∧ s' = s) ∨ (s ∉ F ∧ s' = u))
    (hright :
      (t ∉ F ∧ ProperInitialSegment t t' ∧ t' ∈ PrefixTree F ∧
        ∃ n, t' = insert n t ∧ u' = insert n u) ∨
      (t ∈ F ∧ t' = t ∧
        ∃ k, (∀ j, j ∈ u → j < k) ∧ u' = insert k u)) :
    FrontBridge F s' t' u' ∧
      s' ∈ PrefixTree F ∧
      (s ∈ F → s' = s) ∧
      (s ∉ F → ProperInitialSegment s s') := by
-- BODY
  sorry
