import Tablet.PowerIResponse
import Tablet.PowerRelAtomAtom
import Tablet.PowerRelAtomNode
import Tablet.PowerRelNodeAtom
import Tablet.PowerRelNodeNode

universe u

-- [TABLET NODE: PowerIResponseWitness]
theorem PowerIResponseWitness {Q : Type u} (r : Q → Q → Prop)
    {x y : PowerQ Q} :
    ¬ PowerRel r x y →
      ∃ x', PowerMove x x' ∧
        ∀ y', PowerMove y y' → ¬ PowerRel r x' y' := by
-- BODY
  intro hxy
  cases x with
  | atom q =>
      cases y with
      | atom q' =>
          refine ⟨.atom q, ?_, ?_⟩
          · rfl
          · intro y' hy'
            change y' = .atom q' at hy'
            subst y'
            exact hxy
      | node ι hι g =>
          rw [PowerRelAtomNode] at hxy
          refine ⟨.atom q, ?_, ?_⟩
          · rfl
          · intro y' hy'
            change PowerChild y' (.node ι hι g) at hy'
            rcases hy' with ⟨i, rfl⟩
            intro hq
            exact hxy ⟨i, hq⟩
  | node ι hι f =>
      cases y with
      | atom q =>
          rw [PowerRelNodeAtom] at hxy
          have hi : ∃ i, ¬ PowerRel r (f i) (.atom q) := by
            classical
            exact Classical.not_forall.mp hxy
          rcases hi with ⟨i, hi⟩
          refine ⟨f i, ?_, ?_⟩
          · change PowerChild (f i) (.node ι hι f)
            exact ⟨i, rfl⟩
          · intro y' hy'
            change y' = .atom q at hy'
            subst y'
            exact hi
      | node κ hκ g =>
          rw [PowerRelNodeNode] at hxy
          have hi : ∃ i, ∀ j, ¬ PowerRel r (f i) (g j) := by
            classical
            rcases Classical.not_forall.mp hxy with ⟨i, hi⟩
            refine ⟨i, ?_⟩
            intro j hij
            exact hi ⟨j, hij⟩
          rcases hi with ⟨i, hi⟩
          refine ⟨f i, ?_, ?_⟩
          · change PowerChild (f i) (.node ι hι f)
            exact ⟨i, rfl⟩
          · intro y' hy'
            change PowerChild y' (.node κ hκ g) at hy'
            rcases hy' with ⟨j, rfl⟩
            exact hi j
