import Tablet.HerCtblCode
import Tablet.PowerQ

universe u

-- [TABLET NODE: HerCtblCodeErase]
def HerCtblCodeErase {Q : Type u} : HerCtblCode Q → PowerQ Q :=
-- BODY
  fun c => match c with
    | .atom q => .atom q
    | .node f =>
        .node (ULift.{u} Nat) ⟨ULift.up 0⟩ (fun i => HerCtblCodeErase (f i.down))
