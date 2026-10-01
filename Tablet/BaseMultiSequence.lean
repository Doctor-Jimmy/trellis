import Tablet.BaseIncSeq

-- [TABLET NODE: BaseMultiSequence]
abbrev BaseMultiSequence (X : Set Nat) (E : Type) :=
-- BODY
  BaseIncSeq X → E
