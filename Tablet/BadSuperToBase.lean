import Tablet.BaseBad
import Tablet.BaseLocallyConstant
import Tablet.BadSuperSequence
import Tablet.SuperSequenceExtension

-- [TABLET NODE: BadSuperToBase]
theorem BadSuperToBase {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q) :
    BadSuperSequence r f →
      ∃ h : BaseMultiSequence X Q,
        BaseLocallyConstant h ∧ BaseBad r h := by
-- BODY
  sorry
