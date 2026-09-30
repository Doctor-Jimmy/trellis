import Tablet.Front
import Tablet.Ray
import Tablet.TailSet

-- [TABLET NODE: FrontRayClosure]
theorem FrontRayClosure (F : Set (Finset Nat)) (X : Set Nat)
    (hF : Front F X) (htriv : F ≠ {∅}) :
    (∀ n ∈ X, Front (Ray F n) (TailSet X n)) ∧
      F = {s | ∃ n ∈ X, ∃ t ∈ Ray F n, s = insert n t} := by
-- BODY
  sorry
