import Tablet.BaseMultiSequence
import Tablet.IncSeqComp
import Tablet.MultiSequence

-- [TABLET NODE: BaseRestrict]
def BaseRestrict {X : Set Nat} {E : Type} (h : BaseMultiSequence X E)
    (z : BaseIncSeq X) : MultiSequence E :=
-- BODY
  fun x => h ⟨IncSeqComp z.1 x, by
    intro n hn
    rcases hn with ⟨m, hm⟩
    apply z.2
    exact ⟨x m, hm⟩⟩
