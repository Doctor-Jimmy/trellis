import Tablet.IncSeq

universe u

-- [TABLET NODE: MultiSequence]
abbrev MultiSequence (E : Type u) :=
-- BODY
  IncSeq → E
