import Tablet.IncSeq

-- [TABLET NODE: PrefixAgree]
def PrefixAgree (n : Nat) (x y : IncSeq) : Prop :=
-- BODY
  ∀ i, i < n → x i = y i
