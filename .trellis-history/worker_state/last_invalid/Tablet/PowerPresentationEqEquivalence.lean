import Tablet.PowerPresentationEq

universe u

-- [TABLET NODE: PowerPresentationEqEquivalence]
theorem PowerPresentationEqEquivalence {Q : Type u} :
    Equivalence (@PowerPresentationEq Q) := by
-- BODY
  have hrefl : ∀ x : PowerQ Q, PowerPresentationEq x x := by
    intro x
    induction x with
    | atom q =>
        rfl
    | node ι h f ih =>
        constructor
        · intro i
          exact ⟨i, ih i⟩
        · intro i
          exact ⟨i, ih i⟩
  have hsymm : ∀ ⦃x y : PowerQ Q⦄,
      PowerPresentationEq x y → PowerPresentationEq y x := by
    intro x
    induction x with
    | atom q =>
        intro y hxy
        cases y with
        | atom q' =>
            exact hxy.symm
        | node ι h g =>
            exact False.elim hxy
    | node ι h f ih =>
        intro y hxy
        cases y with
        | atom q =>
            exact False.elim hxy
        | node κ hk g =>
            constructor
            · intro j
              obtain ⟨i, hij⟩ := hxy.2 j
              exact ⟨i, ih i (y := g j) hij⟩
            · intro i
              obtain ⟨j, hij⟩ := hxy.1 i
              exact ⟨j, ih i (y := g j) hij⟩
  have htrans : ∀ ⦃x y z : PowerQ Q⦄,
      PowerPresentationEq x y →
      PowerPresentationEq y z →
      PowerPresentationEq x z := by
    intro x
    induction x with
    | atom q =>
        intro y z hxy hyz
        cases y with
        | atom q' =>
            cases z with
            | atom q'' =>
                exact hxy.trans hyz
            | node nu h'' k =>
                exact False.elim hyz
        | node κ h' g =>
            exact False.elim hxy
    | node ι h f ih =>
        intro y z hxy hyz
        cases y with
        | atom q =>
            exact False.elim hxy
        | node κ h' g =>
            cases z with
            | atom q =>
                exact False.elim hyz
            | node nu h'' k =>
                constructor
                · intro i
                  obtain ⟨j, hij⟩ := hxy.1 i
                  obtain ⟨l, hjl⟩ := hyz.1 j
                  exact ⟨l, ih i (y := g j) (z := k l) hij hjl⟩
                · intro l
                  obtain ⟨j, hjl⟩ := hyz.2 l
                  obtain ⟨i, hij⟩ := hxy.2 j
                  exact ⟨i, ih i (y := g j) (z := k l) hij hjl⟩
  exact { refl := hrefl, symm := fun h => hsymm h, trans := fun h1 h2 => htrans h1 h2 }
