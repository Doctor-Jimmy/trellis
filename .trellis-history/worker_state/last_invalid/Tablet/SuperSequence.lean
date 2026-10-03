import Tablet.Front

universe u

-- [TABLET NODE: SuperSequence]
structure SuperSequence (F : Set (Finset Nat)) (X : Set Nat) (E : Type u) where
-- BODY
  front : Front F X
  value : F → E
