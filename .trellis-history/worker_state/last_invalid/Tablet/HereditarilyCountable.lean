import Tablet.HerCtblCodeErase
import Tablet.PowerPresentationEq

universe u

-- [TABLET NODE: HereditarilyCountable]
def HereditarilyCountable {Q : Type u} (x : PowerQ Q) : Prop :=
-- BODY
  ∃ c : HerCtblCode Q, PowerPresentationEq x (HerCtblCodeErase c)
