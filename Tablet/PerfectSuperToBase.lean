import Tablet.BaseLocallyConstant
import Tablet.BasePerfect
import Tablet.PerfectSuperSequence
import Tablet.SuperSequenceExtension

-- [TABLET NODE: PerfectSuperToBase]
theorem PerfectSuperToBase {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q) :
    PerfectSuperSequence r f →
      ∃ h : BaseMultiSequence X Q,
        BaseLocallyConstant h ∧
          (∀ x : BaseIncSeq X, ∃ s : Finset Nat, ∃ hs : FrontPrefix F s x.1,
            h x = f.value ⟨s, hs.1⟩) ∧
          BasePerfect r h := by
-- BODY
  sorry
