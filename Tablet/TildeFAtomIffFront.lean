import Tablet.TildeF
import Tablet.TildeFFrontEquation
import Tablet.TildeFNonfrontEquation

universe u

-- [TABLET NODE: TildeFAtomIffFront]
theorem TildeFAtomIffFront {Q : Type u} {F : Set (Finset Nat)}
    (f : SuperSequence F Set.univ Q)
    (s : {s : Finset Nat // s ∈ PrefixTree F}) :
    (∃ q : Q, TildeF f s = PowerQ.atom q) ↔ s.1 ∈ F := by
-- BODY
  sorry
