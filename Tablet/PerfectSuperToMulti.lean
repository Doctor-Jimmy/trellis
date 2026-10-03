import Tablet.DecidingFrontSet
import Tablet.DecidingValue
import Tablet.FiniteShift
import Tablet.Front
import Tablet.InfiniteSetEnumeration
import Tablet.LocallyConstant
import Tablet.PerfectMultiSequence
import Tablet.PerfectSuperSequence
import Tablet.MultiSequenceRestrict
import Tablet.RestrictionShift
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
  classical
  obtain ⟨z, hz⟩ := InfiniteSetEnumeration Y hF'.infinite_base
  refine ⟨z, ?_⟩
  intro x
  let a : IncSeq := IncSeqComp z x
  let b : IncSeq := IncSeqComp z (ShiftMap x)
  have haY : Set.range (a : Nat → Nat) ⊆ Y := by
    intro n hn
    rcases hn with ⟨k, rfl⟩
    rw [← hz]
    exact ⟨x k, by rfl⟩
  have hbY : Set.range (b : Nat → Nat) ⊆ Y := by
    intro n hn
    rcases hn with ⟨k, rfl⟩
    rw [← hz]
    exact ⟨ShiftMap x k, by rfl⟩
  have haInf : (Set.range (a : Nat → Nat)).Infinite :=
    Set.infinite_range_of_injective a.injective
  have hbInf : (Set.range (b : Nat → Nat)).Infinite :=
    Set.infinite_range_of_injective b.injective
  obtain ⟨s, hsF, hsP⟩ := hF'.dense _ haY haInf
  obtain ⟨t, htF, htP⟩ := hF'.dense _ hbY hbInf
  have hsD : s ∈ DecidingFrontSet h := hsub hsF
  have htD : t ∈ DecidingFrontSet h := hsub htF
  have hsa : f.value ⟨s, hsD⟩ = h a := hf ⟨s, hsD⟩ a hsP
  have htb : f.value ⟨t, htD⟩ = h b := hf ⟨t, htD⟩ b htP
  have hab : b = ShiftMap a := by
    dsimp [a, b]
    exact RestrictionShift z x
  have hfin : FiniteShift s t := by
    refine ⟨a, hsP, ?_⟩
    rw [← hab]
    exact htP
  have hrel := hp s t hsF htF hfin
  simpa [MultiSequenceRestrict, SuperSequenceRestrict, a, b, hsa, htb] using hrel
