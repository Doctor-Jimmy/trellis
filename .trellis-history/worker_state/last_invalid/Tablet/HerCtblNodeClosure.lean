import Tablet.HerCtblPower
import Tablet.HerCtblCodeErase
import Tablet.PowerPresentationEqEquivalence

universe u

-- [TABLET NODE: HerCtblNodeClosure]
theorem HerCtblNodeClosure {Q : Type u} {I : Type u}
    [Nonempty I] [Countable I] (f : I → HerCtblPower Q) :
    HereditarilyCountable
      (.node I inferInstance (fun i => (f i).1)) := by
-- BODY
  obtain ⟨e, he⟩ := exists_surjective_nat I
  have hcode : ∀ i : I, ∃ c : HerCtblCode Q,
      PowerPresentationEq (f i).1 (HerCtblCodeErase c) := by
    intro i
    exact (f i).2
  choose c hc using hcode
  let d : HerCtblCode Q := .node (fun n => c (e n))
  refine ⟨d, ?_⟩
  change PowerPresentationEq
    (.node I inferInstance (fun i => (f i).1))
    (.node (ULift.{u} Nat) inferInstance
      (fun n => HerCtblCodeErase (c (e n.down))))
  constructor
  · intro i
    obtain ⟨n, hn⟩ := he i
    refine ⟨ULift.up n, ?_⟩
    simpa [hn] using hc i
  · intro n
    refine ⟨e n.down, ?_⟩
    simpa using PowerPresentationEqEquivalence.symm
      (PowerPresentationEqEquivalence.symm (hc (e n.down)))
