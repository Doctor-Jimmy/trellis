import Tablet.TildeF
import Tablet.FrontTreeImmediateExtensions
import Tablet.HerCtblNodeClosure
import Tablet.TildeFFrontEquation
import Tablet.TildeFNonfrontEquation
import Tablet.HereditarilyCountableAtom

universe u

-- [TABLET NODE: TildeFHerCtbl]
theorem TildeFHerCtbl {Q : Type u} {F : Set (Finset Nat)}
    (f : SuperSequence F Set.univ Q)
    (s : {s : Finset Nat // s ∈ PrefixTree F}) :
    HereditarilyCountable (TildeF f s) := by
-- BODY
  classical
  induction s using (FrontTreeWellFounded F Set.univ f.front).induction with
  | h s ih =>
      by_cases hsF : s.1 ∈ F
      · rw [TildeFFrontEquation f s hsF]
        exact HereditarilyCountableAtom (f.value ⟨s.1, hsF⟩)
      · rw [TildeFNonfrontEquation f s hsF]
        let E : Type := {n : Nat //
          ProperInitialSegment s.1 (insert n s.1) ∧
            insert n s.1 ∈ PrefixTree F}
        have hE : Nonempty E :=
          FrontTreeImmediateExtensions F Set.univ f.front s.1 s.2 hsF |>.1
        letI : Nonempty (ULift.{u} E) :=
          ⟨ULift.up (Classical.choice hE)⟩
        let g : ULift.{u} E → HerCtblPower Q := fun i =>
          ⟨TildeF f ⟨insert i.down.1 s.1, i.down.2.2⟩,
            ih ⟨insert i.down.1 s.1, i.down.2.2⟩ i.down.2.1⟩
        exact HerCtblNodeClosure g
