import Tablet.PowerRelAtomAtom
import Tablet.PowerRelAtomNode
import Tablet.PowerRelNodeAtom
import Tablet.PowerRelNodeNode
import Tablet.PowerPresentationEqEquivalence

universe u

-- [TABLET NODE: PowerRelCongrLeft]
theorem PowerRelCongrLeft {Q : Type u} (r : Q → Q → Prop)
    {x x' y : PowerQ Q} (hxx' : PowerPresentationEq x x') :
    PowerRel r x y ↔ PowerRel r x' y := by
-- BODY
  induction x using PowerChildWellFounded.induction generalizing x' y with
  | h x ih =>
    cases x with
    | atom q =>
      cases x' with
      | atom q' =>
          have hqq : q = q' := hxx'
          subst q'
          exact Iff.rfl
      | node ι h g =>
          exact False.elim hxx'
    | node ι h f =>
      cases x' with
      | atom q =>
          exact False.elim hxx'
      | node κ h' g =>
        change (∀ i, ∃ j, PowerPresentationEq (f i) (g j)) ∧
          (∀ j, ∃ i, PowerPresentationEq (f i) (g j)) at hxx'
        have hx'x : PowerPresentationEq (.node κ h' g) (.node ι h f) :=
          PowerPresentationEqEquivalence.symm hxx'
        change (∀ j, ∃ i, PowerPresentationEq (g j) (f i)) ∧
          (∀ i, ∃ j, PowerPresentationEq (g j) (f i)) at hx'x
        cases y with
        | atom q =>
          rw [PowerRelNodeAtom, PowerRelNodeAtom]
          constructor
          · intro hleft j
            obtain ⟨i, e⟩ := hx'x.1 j
            have e' : PowerPresentationEq (f i) (g j) :=
              PowerPresentationEqEquivalence.symm e
            have hchild : @PowerChild Q (f i) (.node ι h f) := ⟨i, rfl⟩
            exact ((ih (f i) hchild (x' := g j) e')).mp (hleft i)
          · intro hright i
            obtain ⟨j, e⟩ := hx'x.2 i
            have e' : PowerPresentationEq (f i) (g j) :=
              PowerPresentationEqEquivalence.symm e
            have hchild : @PowerChild Q (f i) (.node ι h f) := ⟨i, rfl⟩
            exact ((ih (f i) hchild (x' := g j) e')).mpr (hright j)
        | node ν h'' k =>
          rw [PowerRelNodeNode, PowerRelNodeNode]
          constructor
          · intro hleft j
            obtain ⟨i, e⟩ := hx'x.1 j
            have e' : PowerPresentationEq (f i) (g j) :=
              PowerPresentationEqEquivalence.symm e
            obtain ⟨l, hrel⟩ := hleft i
            have hchild : @PowerChild Q (f i) (.node ι h f) := ⟨i, rfl⟩
            exact ⟨l, (ih (f i) hchild (x' := g j) e').mp hrel⟩
          · intro hright i
            obtain ⟨j, e⟩ := hx'x.2 i
            have e' : PowerPresentationEq (f i) (g j) :=
              PowerPresentationEqEquivalence.symm e
            obtain ⟨l, hrel⟩ := hright j
            have hchild : @PowerChild Q (f i) (.node ι h f) := ⟨i, rfl⟩
            exact ⟨l, (ih (f i) hchild (x' := g j) e').mpr hrel⟩
