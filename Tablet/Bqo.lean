import Tablet.BadMultiSequence
import Tablet.LocallyConstant

universe u

-- [TABLET NODE: Bqo]
def Bqo {Q : Type u} (r : Q → Q → Prop) : Prop :=
-- BODY
  ∀ h : MultiSequence Q, LocallyConstant h → ¬ BadMultiSequence r h
