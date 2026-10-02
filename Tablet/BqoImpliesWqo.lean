import Tablet.Bqo

universe u

-- [TABLET NODE: BqoImpliesWqo]
theorem BqoImpliesWqo {Q : Type u} (r : Q → Q → Prop) :
    Bqo r → WellQuasiOrdered r := by
-- BODY
  intro hb f
  by_contra hn
  have hno : ∀ m n : Nat, m < n → ¬ r (f m) (f n) := by
    intro m n hmn hr
    apply hn
    exact ⟨m, n, hmn, hr⟩
  let h : MultiSequence Q := fun x => f (x 0)
  have hlc : LocallyConstant h := by
    intro x
    refine ⟨1, ?_⟩
    intro y hxy
    dsimp [h]
    congr 1
    exact (hxy 0 (by omega)).symm
  have hbad : BadMultiSequence r h := by
    intro x
    dsimp [BadMultiSequence, h]
    apply hno (x 0) ((ShiftMap x) 0)
    change x 0 < x 1
    exact x.strictMono (by omega)
  exact (hb h hlc) hbad
