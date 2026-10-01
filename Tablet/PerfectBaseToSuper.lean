import Tablet.BaseRestrict
import Tablet.FrontRestriction
import Tablet.PerfectMultiSequence
import Tablet.PerfectSuperSequence
import Tablet.SuperSequenceExtension
import Tablet.SuperSequenceRestrict

-- [TABLET NODE: PerfectBaseToSuper]
theorem PerfectBaseToSuper {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q)
    (h : BaseMultiSequence X Q)
    (hext : ∀ (x : BaseIncSeq X) (s : Finset Nat)
      (hs : FrontPrefix F s x.1), h x = f.value ⟨s, hs.1⟩)
    (z : BaseIncSeq X) (hp : PerfectMultiSequence r (BaseRestrict h z)) :
    ∃ F' : Set (Finset Nat),
      ∃ hF' : Front F' (Set.range (z.1 : Nat → Nat)),
        ∃ hsub : F' ⊆ F,
          PerfectSuperSequence r
            (SuperSequenceRestrict f F' (Set.range (z.1 : Nat → Nat)) hF' hsub) := by
-- BODY
  sorry
