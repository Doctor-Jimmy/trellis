import Tablet.PrefixAgree

-- [TABLET NODE: BaireContinuous]
def BaireContinuous (F : IncSeq → IncSeq) : Prop :=
-- BODY
  ∀ x n, ∃ k, ∀ y, PrefixAgree k x y → PrefixAgree n (F x) (F y)
