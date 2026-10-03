import Tablet.PowerShiftIterPrefixAgree
import Tablet.LocallyConstant

universe u

-- [TABLET NODE: PowerFiniteOrbitConstancy]
theorem PowerFiniteOrbitConstancy {E : Type u} (h : MultiSequence E)
    (hloc : LocallyConstant h) (x : IncSeq) (m : Nat) :
    ∃ N, ∀ y, PrefixAgree N x y →
      ∀ j, j ≤ m →
        h (PowerShiftIter j y) = h (PowerShiftIter j x) := by
-- BODY
  have prefix_mono : ∀ {a b : Nat} {u v : IncSeq}, a ≤ b →
      PrefixAgree b u v → PrefixAgree a u v := by
    intro a b u v hab huv i hi
    exact huv i (lt_of_lt_of_le hi hab)
  induction m with
  | zero =>
      obtain ⟨n, hn⟩ := hloc x
      refine ⟨n, ?_⟩
      intro y hxy j hj
      have hj0 : j = 0 := by omega
      subst j
      simpa [PowerShiftIter] using hn y hxy
  | succ m ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨n, hn⟩ := hloc (PowerShiftIter (Nat.succ m) x)
      let M : Nat := Nat.max N (n + Nat.succ m)
      have hNM : N ≤ M := by
        dsimp [M]
        exact Nat.le_max_left _ _
      have hnmM : n + Nat.succ m ≤ M := by
        dsimp [M]
        exact Nat.le_max_right _ _
      refine ⟨M, ?_⟩
      intro y hxy j hj
      by_cases hjm : j ≤ m
      · exact hN y (prefix_mono hNM hxy) j hjm
      · have hjeq : j = Nat.succ m := by omega
        subst j
        have hshift : PrefixAgree (n + Nat.succ m) x y :=
          prefix_mono hnmM hxy
        have hiter : PrefixAgree n (PowerShiftIter (Nat.succ m) x)
            (PowerShiftIter (Nat.succ m) y) :=
          PowerShiftIterPrefixAgree x y (Nat.succ m) n hshift
        exact hn (PowerShiftIter (Nat.succ m) y) hiter
