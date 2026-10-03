import Tablet.Preamble

-- [TABLET NODE: ProperPrefixSet]
def ProperPrefixSet (s : Finset Nat) (Y : Set Nat) : Prop :=
-- BODY
  ∃ n, n ∈ Y ∧ ∀ k, k ∈ s ↔ k ∈ Y ∧ k < n
