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
  sorry
