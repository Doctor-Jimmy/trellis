import Tablet.Preamble

-- [TABLET NODE: Ray]
def Ray (F : Set (Finset Nat)) (n : Nat) : Set (Finset Nat) :=
-- BODY
  {s | (∀ k ∈ s, n < k) ∧ insert n s ∈ F}
