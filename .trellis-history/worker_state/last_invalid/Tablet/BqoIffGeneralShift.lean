import Tablet.GBetterRelIff
import Tablet.GBetterRel
import Tablet.Bqo
import Tablet.BadMultiSequence
import Tablet.ShiftMap
import Tablet.IncSeqId
import Tablet.RightComp
import Tablet.SuccSeq

-- [TABLET NODE: BqoIffGeneralShift]
theorem BqoIffGeneralShift {Q : Type} (r : Q → Q → Prop)
    (hpre : IsPreorder Q r) :
    Bqo r ↔
      ∀ (phi : IncSeq → Q), LocallyConstant phi →
        ∀ g : IncSeq, ∃ f : IncSeq,
          r (phi f) (phi (RightComp g f)) := by
-- BODY
  constructor
  · intro hbqo phi hphi g
    by_cases hg : g = IncSeqId
    · subst g
      refine ⟨IncSeqId, ?_⟩
      have hid : RightComp IncSeqId IncSeqId = IncSeqId := by
        ext n
        rfl
      rw [hid]
      exact hpre.toRefl.refl _
    · have hgb : GBetterRel g r :=
        ((GBetterRelIff g hg).2 r hpre).mpr hbqo
      rcases hgb.1 phi hphi with ⟨f, H, hH⟩
      refine ⟨f, ?_⟩
      have hfid : IncSeqComp f IncSeqId = f := by
        ext n
        rfl
      have hfg : IncSeqComp f (RightComp g IncSeqId) = RightComp g f := by
        ext n
        rfl
      have hh := H.hom IncSeqId
      rw [hH, hH, hfid, hfg] at hh
      exact hh
  · intro hprop
    unfold Bqo
    intro h hloc hbad
    obtain ⟨f, hf⟩ := hprop h hloc SuccSeq
    apply hbad f
    simpa [ShiftMap] using hf
