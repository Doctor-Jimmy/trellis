import Tablet.BaseIncSeq
import Tablet.ShiftMap

-- [TABLET NODE: BaseShift]
def BaseShift (X : Set Nat) (x : BaseIncSeq X) : BaseIncSeq X :=
-- BODY
  ⟨ShiftMap x.1, by
    intro n hn
    rcases hn with ⟨m, hm⟩
    apply x.2
    refine ⟨SuccSeq m, ?_⟩
    change x.1 (SuccSeq m) = n at hm
    exact hm⟩
