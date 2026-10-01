import Tablet.BaseLocallyConstant
import Tablet.FrontPrefixExists
import Tablet.FrontPrefixUnique
import Tablet.SuperSequence

-- [TABLET NODE: SuperSequenceExtension]
theorem SuperSequenceExtension {E : Type} (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (f : SuperSequence F X E) :
    ∃ h : BaseMultiSequence X E,
      BaseLocallyConstant h ∧
      ∀ x : BaseIncSeq X, ∃ s : Finset Nat, ∃ hs : FrontPrefix F s x.1,
        h x = f.value ⟨s, hs.1⟩ := by
-- BODY
  sorry
