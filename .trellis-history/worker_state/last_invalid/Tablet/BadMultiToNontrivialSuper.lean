import Tablet.BadMultiSequence
import Tablet.BadMultiToSuper
import Tablet.DecidingFront
import Tablet.DecidingFrontSet
import Tablet.DecidingValue
import Tablet.IncSeqId
import Tablet.ShiftMap

universe u

-- [TABLET NODE: BadMultiToNontrivialSuper]
theorem BadMultiToNontrivialSuper {Q : Type u} (r : Q → Q → Prop)
    [Std.Refl r] (h : MultiSequence Q) (hlc : LocallyConstant h)
    (hbad : BadMultiSequence r h) :
    ∃ f : SuperSequence (DecidingFrontSet h) Set.univ Q,
      BadSuperSequence r f ∧ ∅ ∉ DecidingFrontSet h := by
-- BODY
  classical
  obtain ⟨v, hv⟩ := DecidingValue h hlc
  let f : SuperSequence (DecidingFrontSet h) Set.univ Q :=
    ⟨DecidingFront h hlc, v⟩
  refine ⟨f, ?_, ?_⟩
  · exact BadMultiToSuper r h f hv hbad
  · intro hempty
    have hempty' : DecidingPrefix h (∅ : Finset Nat) := hempty.1
    have hprefix : ∀ x : IncSeq,
        ProperPrefixSet (∅ : Finset Nat) (Set.range (x : Nat → Nat)) := by
      intro x
      refine ⟨x 0, ⟨0, rfl⟩, ?_⟩
      intro k
      constructor
      · intro hk
        simpa using hk
      · rintro ⟨⟨i, rfl⟩, hi⟩
        exact False.elim ((Nat.not_lt_of_ge (x.monotone (Nat.zero_le i))) hi)
    have heq : h IncSeqId = h (ShiftMap IncSeqId) :=
      hempty' IncSeqId (ShiftMap IncSeqId)
        (hprefix IncSeqId) (hprefix (ShiftMap IncSeqId))
    apply hbad IncSeqId
    rw [heq]
    exact refl _
