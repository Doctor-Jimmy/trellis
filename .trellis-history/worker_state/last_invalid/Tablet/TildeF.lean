import Tablet.FrontTreeImmediateExtensions
import Tablet.FrontTreeWellFounded
import Tablet.PowerQ
import Tablet.SuperSequence

universe u

-- [TABLET NODE: TildeF]
noncomputable def TildeF {Q : Type u} {F : Set (Finset Nat)}
    (f : SuperSequence F Set.univ Q) :
    {s : Finset Nat // s ∈ PrefixTree F} → PowerQ Q := by
-- BODY
  classical
  exact WellFounded.fix (FrontTreeWellFounded F Set.univ f.front)
    (fun s rec =>
      if hs : s.1 ∈ F then
        PowerQ.atom (f.value ⟨s.1, hs⟩)
      else
        let E := {n : Nat // ProperInitialSegment s.1 (insert n s.1) ∧
          insert n s.1 ∈ PrefixTree F}
        PowerQ.node (ULift.{u} E)
          ⟨ULift.up (Classical.choice
            (FrontTreeImmediateExtensions F Set.univ f.front s.1 s.2 hs).1)⟩
          (fun i =>
            rec ⟨insert i.down.1 s.1, i.down.2.2⟩
              i.down.2.1))
