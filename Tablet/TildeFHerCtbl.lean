import Tablet.TildeF
import Tablet.FrontTreeImmediateExtensions
import Tablet.HerCtblNodeClosure
import Tablet.TildeFFrontEquation
import Tablet.TildeFNonfrontEquation
import Tablet.HereditarilyCountableAtom

universe u

-- [TABLET NODE: TildeFHerCtbl]
theorem TildeFHerCtbl {Q : Type u} {F : Set (Finset Nat)}
    (f : SuperSequence F Set.univ Q)
    (s : {s : Finset Nat // s ∈ PrefixTree F}) :
    HereditarilyCountable (TildeF f s) := by
-- BODY
  sorry
