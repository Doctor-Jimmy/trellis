import Tablet.TildeFSingleton
import Tablet.HerCtblRel
import Tablet.FrontBridgeInit
import Tablet.FrontBridgeStep
import Tablet.FrontBridgeTerminal
import Tablet.BadSuperSequence
import Tablet.PowerRelAtomAtom
import Tablet.PowerRelAtomNode
import Tablet.PowerRelNodeAtom
import Tablet.PowerRelNodeNode

universe u

-- [TABLET NODE: ConverseGame]
theorem ConverseGame {Q : Type u} {F : Set (Finset Nat)}
    (r : Q → Q → Prop) (f : SuperSequence F Set.univ Q)
    (htriv : ∅ ∉ F) (hbad : BadSuperSequence r f) :
    ∀ m n : Nat, m < n →
      ¬ HerCtblRel r
        ⟨TildeFSingleton f htriv m,
          TildeFHerCtbl f
            ⟨{m}, FrontTreeSingleton F f.front htriv m⟩⟩
        ⟨TildeFSingleton f htriv n,
          TildeFHerCtbl f
            ⟨{n}, FrontTreeSingleton F f.front htriv n⟩⟩ := by
-- BODY
  sorry
