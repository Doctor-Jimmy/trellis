import Tablet.BadMultiSequence
import Tablet.LocallyConstant

-- [TABLET NODE: Bqo]
def Bqo {Q : Type} (r : Q → Q → Prop) : Prop :=
-- BODY
  ∀ h : MultiSequence Q, LocallyConstant h → ¬ BadMultiSequence r h
