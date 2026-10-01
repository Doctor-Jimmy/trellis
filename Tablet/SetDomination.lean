import Tablet.Preamble

-- [TABLET NODE: SetDomination]
def SetDomination {Q : Type} (r : Q → Q → Prop) (P T : Set Q) : Prop :=
-- BODY
  ∀ p ∈ P, ∃ q ∈ T, r p q

