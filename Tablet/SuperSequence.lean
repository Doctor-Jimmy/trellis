import Tablet.Front

-- [TABLET NODE: SuperSequence]
structure SuperSequence (F : Set (Finset Nat)) (X : Set Nat) (E : Type) where
-- BODY
  front : Front F X
  value : F → E
