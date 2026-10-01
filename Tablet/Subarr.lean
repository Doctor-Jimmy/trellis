import Tablet.BadMultiRestrict
import Tablet.BadMultiToSuper
import Tablet.BadSuperRestrict
import Tablet.BaseBqoRestriction
import Tablet.DecidingFront
import Tablet.DecidingValue
import Tablet.NoBadPerfectSuper
import Tablet.PerfectBaseToSuper
import Tablet.PerfectSuperToMulti
import Tablet.RestrictionLocallyConstant
import Tablet.ShiftDichotomy
import Tablet.SuperSequenceExtension

-- [TABLET NODE: Subarr]
theorem Subarr {Q : Type} (r : Q → Q → Prop) [IsPreorder Q r] :
    Bqo r ↔
      (∀ (X : Set Nat), X.Infinite →
        ∀ h : BaseMultiSequence X Q, BaseLocallyConstant h →
          ∃ z : BaseIncSeq X,
            PerfectMultiSequence r (BaseRestrict h z)) ∧
      (∀ (F : Set (Finset Nat)) (X : Set Nat)
          (f : SuperSequence F X Q),
        ∃ F' : Set (Finset Nat), ∃ Y : Set Nat,
          ∃ hF' : Front F' Y, ∃ hsub : F' ⊆ F,
            PerfectSuperSequence r (SuperSequenceRestrict f F' Y hF' hsub)) := by
-- BODY
  sorry
