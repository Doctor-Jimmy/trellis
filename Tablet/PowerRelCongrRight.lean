import Tablet.PowerRelCongrLeft

universe u

-- [TABLET NODE: PowerRelCongrRight]
theorem PowerRelCongrRight {Q : Type u} (r : Q → Q → Prop)
    {x y y' : PowerQ Q} (hyy' : PowerPresentationEq y y') :
    PowerRel r x y ↔ PowerRel r x y' := by
-- BODY
  induction y using PowerChildWellFounded.induction generalizing x y' with
  | h y ih =>
    cases y with
    | atom q =>
      cases y' with
      | atom q' =>
          have hqq : q = q' := hyy'
          subst q'
          exact Iff.rfl
      | node ι h g =>
          exact False.elim hyy'
    | node ι h f =>
      cases y' with
      | atom q =>
          exact False.elim hyy'
      | node κ h' g =>
        change (∀ i, ∃ j, PowerPresentationEq (f i) (g j)) ∧
          (∀ j, ∃ i, PowerPresentationEq (f i) (g j)) at hyy'
        cases x with
        | atom q =>
          rw [PowerRelAtomNode, PowerRelAtomNode]
          constructor
          · intro hleft
            obtain ⟨i, hrel⟩ := hleft
            obtain ⟨j, e⟩ := hyy'.1 i
            have hchild : @PowerChild Q (f i) (.node ι h f) := ⟨i, rfl⟩
            exact ⟨j, (ih (f i) hchild (x := .atom q) (y' := g j) e).mp hrel⟩
          · intro hright
            obtain ⟨j, hrel⟩ := hright
            obtain ⟨i, e⟩ := hyy'.2 j
            have hchild : @PowerChild Q (f i) (.node ι h f) := ⟨i, rfl⟩
            exact ⟨i, (ih (f i) hchild (x := .atom q) (y' := g j) e).mpr hrel⟩
        | node μ h'' k =>
          rw [PowerRelNodeNode, PowerRelNodeNode]
          constructor
          · intro hleft i
            obtain ⟨j, hrel⟩ := hleft i
            obtain ⟨j', e⟩ := hyy'.1 j
            have hchild : @PowerChild Q (f j) (.node ι h f) := ⟨j, rfl⟩
            exact ⟨j', (ih (f j) hchild (x := k i) (y' := g j') e).mp hrel⟩
          · intro hright i
            obtain ⟨j', hrel⟩ := hright i
            obtain ⟨j, e⟩ := hyy'.2 j'
            have hchild : @PowerChild Q (f j) (.node ι h f) := ⟨j, rfl⟩
            exact ⟨j, (ih (f j) hchild (x := k i) (y' := g j') e).mpr hrel⟩
