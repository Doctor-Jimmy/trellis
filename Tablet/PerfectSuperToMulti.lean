import Tablet.DecidingFrontSet
import Tablet.LocallyConstant
import Tablet.PerfectMultiSequence
import Tablet.PerfectSuperSequence
import Tablet.MultiSequenceRestrict
import Tablet.SuperSequenceRestrict

-- [TABLET NODE: PerfectSuperToMulti]
theorem PerfectSuperToMulti {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) (hlc : LocallyConstant h)
    (f : SuperSequence (DecidingFrontSet h) Set.univ Q)
    (hf : ∀ (s : DecidingFrontSet h) (x : IncSeq),
      ProperPrefixSet s.1 (Set.range (x : Nat → Nat)) → f.value s = h x)
    (F' : Set (Finset Nat)) (Y : Set Nat) (hF' : Front F' Y)
    (hsub : F' ⊆ DecidingFrontSet h)
    (hp : PerfectSuperSequence r
      (SuperSequenceRestrict f F' Y hF' hsub)) :
    ∃ z : IncSeq, PerfectMultiSequence r (MultiSequenceRestrict h z) := by
-- BODY
  sorry
