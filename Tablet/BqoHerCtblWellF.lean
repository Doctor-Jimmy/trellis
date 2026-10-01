import Tablet.BqoHerCtblWqo
import Tablet.HerCtblWqoIffWellFounded

universe u

-- [TABLET NODE: BqoHerCtblWellF]
theorem BqoHerCtblWellF {Q : Type u} (r : Q → Q → Prop)
    [IsPreorder Q r] :
    Bqo r ↔ WellFounded (fun a b : HerCtblPower Q =>
      HerCtblRel r a b ∧ ¬ HerCtblRel r b a) := by
-- BODY
  exact (BqoHerCtblWqo r).trans (HerCtblWqoIffWellFounded r)
