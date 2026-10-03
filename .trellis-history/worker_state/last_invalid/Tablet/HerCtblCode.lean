import Tablet.Preamble

universe u

-- [TABLET NODE: HerCtblCode]
inductive HerCtblCode (Q : Type u) : Type (u + 1) where
-- BODY
  | atom : Q → HerCtblCode Q
  | node : (Nat → HerCtblCode Q) → HerCtblCode Q
