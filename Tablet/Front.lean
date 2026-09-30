import Tablet.InitialSegment
import Tablet.FrontBase
import Tablet.ProperPrefixSet

-- [TABLET NODE: Front]
structure Front (F : Set (Finset Nat)) (X : Set Nat) : Prop where
-- BODY
  infinite_base : X.Infinite
  base_condition : F = {∅} ∨ FrontBase F = X
  prefix_free : ∀ ⦃s t : Finset Nat⦄, s ∈ F → t ∈ F →
    InitialSegment s t → s = t
  dense : ∀ Y : Set Nat, Y ⊆ X → Y.Infinite →
    ∃ s : Finset Nat, s ∈ F ∧ ProperPrefixSet s Y
