import Tablet.ContinuousRelHom
import Tablet.ShiftMap

-- [TABLET NODE: BetterRel]
def BetterRel {A : Type} (r : A → A → Prop) : Prop :=
-- BODY
  ¬ Nonempty (ContinuousRelHom ShiftMap (fun a b => ¬ r a b))
