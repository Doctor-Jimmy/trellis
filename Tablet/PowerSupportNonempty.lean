import Tablet.PowerSupport

universe u

-- [TABLET NODE: PowerSupportNonempty]
theorem PowerSupportNonempty {Q : Type u} (x : PowerQ Q) :
    (PowerSupport x).Nonempty := by
-- BODY
  induction x with
  | atom q =>
      exact ⟨q, by simp [PowerSupport]⟩
  | node ι h f ih =>
      rcases h with ⟨i⟩
      rcases ih i with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      exact Set.mem_iUnion.2 ⟨i, hq⟩
