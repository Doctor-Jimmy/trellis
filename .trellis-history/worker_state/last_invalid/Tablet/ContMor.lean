import Tablet.ContinuousHom

-- [TABLET NODE: ContMor]
def ContMor (r s : IncSeq → IncSeq) : Prop :=
-- BODY
  Nonempty (ContinuousHom r s)
