import Tablet.BaseIncSeq
import Tablet.RightComp

-- [TABLET NODE: BaseRightComp]
def BaseRightComp (X : Set Nat) (z : IncSeq) (x : BaseIncSeq X) : BaseIncSeq X :=
-- BODY
  ⟨RightComp z x.1, by
    intro n hn
    rcases hn with ⟨m, hm⟩
    apply x.2
    exact ⟨z m, hm⟩⟩
