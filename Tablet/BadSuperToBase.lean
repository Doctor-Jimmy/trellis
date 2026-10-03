import Tablet.BaseBad
import Tablet.BaseIncSeq
import Tablet.BaseLocallyConstant
import Tablet.BaseShift
import Tablet.BadSuperSequence
import Tablet.FiniteShift
import Tablet.FrontPrefix
import Tablet.ProperPrefixSet
import Tablet.SuperSequence
import Tablet.SuperSequenceExtension

-- [TABLET NODE: BadSuperToBase]
theorem BadSuperToBase {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q) :
    BadSuperSequence r f →
      ∃ h : BaseMultiSequence X Q,
        BaseLocallyConstant h ∧
          (∀ x : BaseIncSeq X, ∃ s : Finset Nat, ∃ hs : FrontPrefix F s x.1,
            h x = f.value ⟨s, hs.1⟩) ∧
          BaseBad r h := by
-- BODY
  intro hbad
  obtain ⟨h, hlc, hext⟩ := SuperSequenceExtension F X f.front f
  refine ⟨h, hlc, hext, ?_⟩
  intro x
  obtain ⟨s, hs, hsval⟩ := hext x
  obtain ⟨t, ht, htval⟩ := hext (BaseShift X x)
  have hshift : FiniteShift s t := by
    refine ⟨x.1, hs.2, ?_⟩
    simpa [BaseShift] using ht.2
  have hbadst := hbad s t hs.1 ht.1 hshift
  rw [← hsval, ← htval] at hbadst
  exact hbadst
