import Tablet.IncSeq

-- [TABLET NODE: SuccSeq]
def SuccSeq : IncSeq :=
-- BODY
  OrderEmbedding.ofStrictMono (fun n : Nat => n + 1) (by
    intro a b hab
    exact Nat.add_lt_add_right hab 1)
