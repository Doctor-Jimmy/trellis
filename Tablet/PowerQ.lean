import Tablet.Preamble

universe u

-- [TABLET NODE: PowerQ]
inductive PowerQ (Q : Type u) : Type (u + 1) where
-- BODY
  | atom : Q → PowerQ Q
  | node : (ι : Type u) → Nonempty ι → (ι → PowerQ Q) → PowerQ Q
