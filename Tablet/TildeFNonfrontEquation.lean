import Tablet.TildeF
import Tablet.FrontTreeImmediateExtensions

universe u

-- [TABLET NODE: TildeFNonfrontEquation]
theorem TildeFNonfrontEquation {Q : Type u} {F : Set (Finset Nat)}
    (f : SuperSequence F Set.univ Q)
    (s : {s : Finset Nat // s ∈ PrefixTree F}) (hs : s.1 ∉ F) :
    TildeF f s =
      PowerQ.node (ULift.{u} {n : Nat //
        ProperInitialSegment s.1 (insert n s.1) ∧
          insert n s.1 ∈ PrefixTree F})
        (by
          exact ⟨ULift.up (Classical.choice
            (FrontTreeImmediateExtensions F Set.univ f.front s.1 s.2 hs).1)⟩)
        (fun i => TildeF f ⟨insert i.down.1 s.1, i.down.2.2⟩) := by
-- BODY
  sorry
