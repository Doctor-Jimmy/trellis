import Tablet.TildeF
import Tablet.SuperSequence

universe u

-- [TABLET NODE: TildeFFrontEquation]
theorem TildeFFrontEquation {Q : Type u} {F : Set (Finset Nat)}
    (f : SuperSequence F Set.univ Q)
    (s : {s : Finset Nat // s ∈ PrefixTree F}) (hs : s.1 ∈ F) :
    TildeF f s = PowerQ.atom (f.value ⟨s.1, hs⟩) := by
-- BODY
  sorry
