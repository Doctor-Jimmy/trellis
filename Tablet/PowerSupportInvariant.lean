import Tablet.PowerPresentationEq
import Tablet.PowerSupport

universe u

-- [TABLET NODE: PowerSupportInvariant]
theorem PowerSupportInvariant {Q : Type u} {x y : PowerQ Q} :
    PowerPresentationEq x y → PowerSupport x = PowerSupport y := by
-- BODY
  induction x generalizing y with
  | atom q =>
      intro hxy
      cases y with
      | atom q' =>
          change q = q' at hxy
          subst q'
          rfl
      | node ι h g =>
          change False at hxy
          exact False.elim hxy
  | node ι h f ih =>
      intro hxy
      cases y with
      | atom q =>
          change False at hxy
          exact False.elim hxy
      | node κ hk g =>
          change (∀ i, ∃ j, PowerPresentationEq (f i) (g j)) ∧
            (∀ j, ∃ i, PowerPresentationEq (f i) (g j)) at hxy
          apply Set.ext
          intro q
          constructor
          · intro hq
            change q ∈ ⋃ i, PowerSupport (f i) at hq
            obtain ⟨i, hqi⟩ := Set.mem_iUnion.1 hq
            obtain ⟨j, hij⟩ := hxy.1 i
            have hqj : q ∈ PowerSupport (g j) := by
              rw [← ih i (y := g j) hij]
              exact hqi
            exact Set.mem_iUnion.2 ⟨j, hqj⟩
          · intro hq
            change q ∈ ⋃ j, PowerSupport (g j) at hq
            obtain ⟨j, hqj⟩ := Set.mem_iUnion.1 hq
            obtain ⟨i, hij⟩ := hxy.2 j
            have hqi : q ∈ PowerSupport (f i) := by
              rw [ih i (y := g j) hij]
              exact hqj
            exact Set.mem_iUnion.2 ⟨i, hqi⟩
