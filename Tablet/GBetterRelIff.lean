import Tablet.BetterRel
import Tablet.GBetterRel
import Tablet.Bqo
import Tablet.MainProp
import Tablet.IncSeqId

-- [TABLET NODE: GBetterRelIff]
theorem GBetterRelIff (g : IncSeq) (hg : g ≠ IncSeqId) :
    (∀ {A : Type} (r : A → A → Prop),
      GBetterRel g r ↔ BetterRel r) ∧
    (∀ {Q : Type} (r : Q → Q → Prop), IsPreorder Q r →
      (GBetterRel g r ↔ Bqo r)) := by
-- BODY
  sorry
