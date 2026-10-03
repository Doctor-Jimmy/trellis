import Tablet.BadMultiSequence
import Tablet.BadSuperSequence
import Tablet.DecidingPrefix
import Tablet.DecidingFrontSet
import Tablet.DecidingValue

universe u

-- [TABLET NODE: BadMultiToSuper]
theorem BadMultiToSuper {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence Q) (f : SuperSequence (DecidingFrontSet h) Set.univ Q)
    (hf : ∀ (s : DecidingFrontSet h) (x : IncSeq),
      ProperPrefixSet s.1 (Set.range (x : Nat → Nat)) → f.value s = h x)
    (hh : BadMultiSequence r h) :
    BadSuperSequence r f := by
-- BODY
  intro s t hs ht hst hrel
  rcases hst with ⟨x, hsx, htx⟩
  rw [hf ⟨s, hs⟩ x hsx, hf ⟨t, ht⟩ (ShiftMap x) htx] at hrel
  exact hh x hrel
