import Tablet.DecidingFront
import Tablet.DecidingValue
import Tablet.BadMultiSequence
import Tablet.MultiSequenceRestrict
import Tablet.RestrictionShift
import Tablet.NashWilliams
import Tablet.PerfectMultiSequence
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: ShiftDichotomy]
theorem ShiftDichotomy {Q : Type} (r : Q → Q → Prop)
    (h : MultiSequence Q) (hlc : LocallyConstant h) :
    ∃ z : IncSeq,
      PerfectMultiSequence r (MultiSequenceRestrict h z) ∨
        BadMultiSequence r (MultiSequenceRestrict h z) := by
-- BODY
  classical
  let c : MultiSequence Bool :=
    fun x => if r (h x) (h (ShiftMap x)) then true else false
  have hc : LocallyConstant c := by
    intro x
    obtain ⟨n, hn⟩ := hlc x
    obtain ⟨m, hm⟩ := hlc (ShiftMap x)
    refine ⟨max n (m + 1), ?_⟩
    intro y hxy
    have hxy_n : PrefixAgree n x y := by
      intro i hi
      exact hxy i (lt_of_lt_of_le hi (Nat.le_max_left _ _))
    have hxy_shift : PrefixAgree m (ShiftMap x) (ShiftMap y) := by
      intro i hi
      change x (i + 1) = y (i + 1)
      exact hxy (i + 1) (by omega)
    have hhy : h y = h x := hn y hxy_n
    have hshy : h (ShiftMap y) = h (ShiftMap x) :=
      hm (ShiftMap y) hxy_shift
    simp [c, hhy, hshy]
  have hfront : Front (DecidingFrontSet c) Set.univ :=
    DecidingFront c hc
  obtain ⟨v, hv⟩ := DecidingValue c hc
  let S : Set (Finset Nat) :=
    {s | ∃ hs : s ∈ DecidingFrontSet c, v ⟨s, hs⟩ = true}
  have hS : S ⊆ DecidingFrontSet c := by
    intro s hs
    exact (by rcases hs with ⟨hs, _⟩; exact hs)
  obtain ⟨F', Y, hF', hFsub, hhom⟩ :=
    NashWilliams (DecidingFrontSet c) Set.univ hfront S hS
  obtain ⟨z, hz⟩ := InfiniteSetEnumeration Y hF'.infinite_base
  refine ⟨z, ?_⟩
  have hcase : ∀ x : IncSeq,
      ∃ s : Finset Nat, s ∈ F' ∧
        ProperPrefixSet s (Set.range (IncSeqComp z x : Nat → Nat)) := by
    intro x
    let u : IncSeq := IncSeqComp z x
    have huY : Set.range (u : Nat → Nat) ⊆ Y := by
      intro a ha
      rcases ha with ⟨k, rfl⟩
      change z (x k) ∈ Y
      rw [← hz]
      exact ⟨x k, rfl⟩
    have huinf : (Set.range (u : Nat → Nat)).Infinite :=
      Set.infinite_range_of_injective u.injective
    obtain ⟨s, hsF', hs⟩ := hF'.dense _ huY huinf
    exact ⟨s, hsF', by simpa [u] using hs⟩
  rcases hhom with hAll | hDisj
  · left
    intro x
    obtain ⟨s, hsF', hs⟩ := hcase x
    obtain ⟨hsF, htrue⟩ := hAll hsF'
    have hcv : c (IncSeqComp z x) = true := by
      calc
        c (IncSeqComp z x) = v ⟨s, hsF⟩ := (hv ⟨s, hsF⟩ _ hs).symm
        _ = true := htrue
    have hrel : r (h (IncSeqComp z x))
        (h (ShiftMap (IncSeqComp z x))) := by
      by_contra hnr
      simp [c, hnr] at hcv
    change r ((MultiSequenceRestrict h z) x)
      ((MultiSequenceRestrict h z) (ShiftMap x))
    rw [show (MultiSequenceRestrict h z) x = h (IncSeqComp z x) by rfl]
    rw [show (MultiSequenceRestrict h z) (ShiftMap x) =
      h (IncSeqComp z (ShiftMap x)) by rfl]
    rw [RestrictionShift]
    exact hrel
  · right
    intro x
    obtain ⟨s, hsF', hs⟩ := hcase x
    have hsnot : s ∉ S := by
      intro hsS
      have hmem : s ∈ (∅ : Set (Finset Nat)) := by
        rw [← hDisj]
        exact ⟨hsF', hsS⟩
      simpa using hmem
    have hcv : c (IncSeqComp z x) ≠ true := by
      intro hc'
      apply hsnot
      exact ⟨hFsub hsF', (hv ⟨s, hFsub hsF'⟩ _ hs).trans hc'⟩
    have hnrel : ¬ r (h (IncSeqComp z x))
        (h (ShiftMap (IncSeqComp z x))) := by
      intro hrel
      apply hcv
      simp [c, hrel]
    change ¬ r ((MultiSequenceRestrict h z) x)
      ((MultiSequenceRestrict h z) (ShiftMap x))
    rw [show (MultiSequenceRestrict h z) x = h (IncSeqComp z x) by rfl]
    rw [show (MultiSequenceRestrict h z) (ShiftMap x) =
      h (IncSeqComp z (ShiftMap x)) by rfl]
    rw [RestrictionShift]
    exact hnrel
