import Tablet.ContMor

-- [TABLET NODE: ContMorEq]
def ContMorEq (r s : IncSeq → IncSeq) : Prop :=
-- BODY
  ContMor r s ∧ ContMor s r
