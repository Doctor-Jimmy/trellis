import Tablet.TildeF
import Tablet.TildeFHerCtbl
import Tablet.FrontTreeSingleton

universe u

-- [TABLET NODE: TildeFSingleton]
noncomputable def TildeFSingleton {Q : Type u} {F : Set (Finset Nat)}
    (f : SuperSequence F Set.univ Q) (htriv : ∅ ∉ F) : Nat → PowerQ Q :=
-- BODY
  fun n => TildeF f ⟨{n}, FrontTreeSingleton F f.front htriv n⟩
