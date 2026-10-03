import Tablet.Bqo
import Tablet.BaseLocallyConstant
import Tablet.RestrictionLocallyConstant
import Tablet.BaseRestrict
import Tablet.PerfectMultiSequence
import Tablet.ShiftDichotomy
import Tablet.InfiniteSetEnumeration

-- [TABLET NODE: BaseBqoRestriction]
theorem BaseBqoRestriction {Q : Type} (r : Q → Q → Prop)
    [IsPreorder Q r] (hb : Bqo r) (X : Set Nat) (hX : X.Infinite)
    (h : BaseMultiSequence X Q) (hlc : BaseLocallyConstant h) :
    ∃ z : BaseIncSeq X, PerfectMultiSequence r (BaseRestrict h z) := by
-- BODY
  classical
  obtain ⟨e, he⟩ := InfiniteSetEnumeration X hX
  let lift : IncSeq → BaseIncSeq X := fun x =>
    ⟨IncSeqComp e x, by
      intro n hn
      rcases hn with ⟨i, rfl⟩
      rw [← he]
      exact ⟨x i, by simp [IncSeqComp]⟩⟩
  let h' : MultiSequence Q := fun x => h (lift x)
  have hlc' : LocallyConstant h' := by
    intro x
    obtain ⟨n, hn⟩ := hlc (lift x)
    refine ⟨n, ?_⟩
    intro y hy
    apply hn
    intro i hi
    change IncSeqComp e x i = IncSeqComp e y i
    simp only [IncSeqComp]
    exact congrArg e (hy i hi)
  obtain ⟨u, hu | hu⟩ := ShiftDichotomy r h' hlc'
  · refine ⟨lift u, ?_⟩
    have hval (x : IncSeq) :
        BaseRestrict h (lift u) x = h' (IncSeqComp u x) := by
      change h ⟨IncSeqComp (lift u).1 x, _⟩ = h (lift (IncSeqComp u x))
      congr 1
    intro x
    rw [hval x, hval (ShiftMap x)]
    simpa [MultiSequenceRestrict] using hu x
  · have hlc_restrict :
        LocallyConstant (MultiSequenceRestrict h' u) :=
      RestrictionLocallyConstant h' u hlc'
    exact (hb _ hlc_restrict hu).elim
