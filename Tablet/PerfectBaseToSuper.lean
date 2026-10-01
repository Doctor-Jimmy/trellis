import Tablet.BasePerfect
import Tablet.BaseRestrict
import Tablet.InfiniteSetEnumeration
import Tablet.FrontRestriction
import Tablet.PerfectSuperSequence
import Tablet.SuperSequenceExtension
import Tablet.SuperSequenceRestrict

-- [TABLET NODE: PerfectBaseToSuper]
theorem PerfectBaseToSuper {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q)
    (h : BaseMultiSequence X Q)
    (hext : ∀ (x : BaseIncSeq X) (s : Finset Nat)
      (hs : FrontPrefix F s x.1), h x = f.value ⟨s, hs.1⟩)
    (z : IncSeq) (hp : BasePerfect r (BaseRestrict h z)) :
    ∃ F' : Set (Finset Nat), ∃ Y : Set Nat,
      ∃ hF' : Front F' Y, ∃ hsub : F' ⊆ F,
        PerfectSuperSequence r (SuperSequenceRestrict f F' Y hF' hsub) := by
-- BODY
  sorry
