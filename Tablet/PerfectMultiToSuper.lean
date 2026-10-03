import Tablet.DecidingPrefix
import Tablet.DecidingFrontSet
import Tablet.PerfectMultiSequence
import Tablet.PerfectSuperSequence

-- [TABLET NODE: PerfectMultiToSuper]
theorem PerfectMultiToSuper {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) (f : SuperSequence (DecidingFrontSet h) Set.univ Q)
    (hf : ∀ (s : DecidingFrontSet h) (x : IncSeq),
      ProperPrefixSet s.1 (Set.range (x : Nat → Nat)) → f.value s = h x)
    (hh : PerfectMultiSequence r h) :
    PerfectSuperSequence r f := by
-- BODY
  intro s t hs ht hst
  rcases hst with ⟨x, hxs, htx⟩
  have hfs : f.value ⟨s, hs⟩ = h x := hf ⟨s, hs⟩ x hxs
  have hft : f.value ⟨t, ht⟩ = h (ShiftMap x) :=
    hf ⟨t, ht⟩ (ShiftMap x) htx
  rw [hfs, hft]
  exact hh x
