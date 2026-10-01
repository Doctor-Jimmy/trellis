import Tablet.BetterRel
import Tablet.GBetterRel
import Tablet.Bqo
import Tablet.MainProp
import Tablet.IncSeqId
import Tablet.IncSeq
import Tablet.PrefixAgree
import Tablet.LocallyConstant
import Tablet.ContinuousRelHom
import Tablet.Front
import Tablet.ProperPrefixSet
import Tablet.DecidingFront
import Tablet.DecidingValue
import Tablet.NashWilliams
import Tablet.InfiniteSetEnumeration
import Tablet.RestrictionLocallyConstant
import Tablet.MultiSequenceRestrict
import Tablet.IncSeqComp
import Tablet.RightComp

-- [TABLET NODE: GBetterRelIff]
theorem GBetterRelIff (g : IncSeq) (hg : g ≠ IncSeqId) :
    (∀ {A : Type} (r : A → A → Prop),
      GBetterRel g r ↔ BetterRel r) ∧
    (∀ {Q : Type} (r : Q → Q → Prop), IsPreorder Q r →
      (GBetterRel g r ↔ Bqo r)) := by
-- BODY
  sorry
