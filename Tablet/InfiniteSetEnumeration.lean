import Tablet.IncSeq

-- [TABLET NODE: InfiniteSetEnumeration]
theorem InfiniteSetEnumeration (X : Set Nat) (hX : X.Infinite) :
    ∃ x : IncSeq, Set.range (x : Nat → Nat) = X := by
-- BODY
  classical
  have h_unbounded : ∀ b : Nat, ∃ m : Nat, m ∈ X ∧ b < m := by
    intro b
    obtain ⟨m, hmX, hm⟩ := hX.exists_notMem_finite (Set.finite_Iic b)
    exact ⟨m, hmX, Nat.lt_of_not_ge (by simpa [Set.mem_Iic] using hm)⟩
  have h_nonempty : ∃ m : Nat, m ∈ X := hX.nonempty
  let next : Nat → Nat := fun a =>
    @Nat.find (fun m : Nat => m ∈ X ∧ a < m) (Classical.decPred _)
      (h_unbounded a)
  let f : Nat → Nat := Nat.rec (Nat.find h_nonempty)
    (fun _ a => next a)
  have hf_zero : f 0 = Nat.find h_nonempty := rfl
  have hf_succ (n : Nat) : f (n + 1) = next (f n) := by
    simp [f]
  have hnext_mem (a : Nat) : next a ∈ X := by
    dsimp [next]
    exact (@Nat.find_spec (fun m : Nat => m ∈ X ∧ a < m) (Classical.decPred _)
      (h_unbounded a)).1
  have hnext_gt (a : Nat) : a < next a := by
    dsimp [next]
    exact (@Nat.find_spec (fun m : Nat => m ∈ X ∧ a < m) (Classical.decPred _)
      (h_unbounded a)).2
  have hnext_le (a m : Nat) (hm : m ∈ X ∧ a < m) : next a ≤ m := by
    dsimp [next]
    exact @Nat.find_min' (fun n : Nat => n ∈ X ∧ a < n) (Classical.decPred _)
      (h_unbounded a) m hm
  have hf_mem : ∀ n : Nat, f n ∈ X := by
    intro n
    induction n with
    | zero =>
        simpa [hf_zero] using (Nat.find_spec h_nonempty)
    | succ n ih =>
        rw [hf_succ]
        exact hnext_mem (f n)
  have hf_step : ∀ n : Nat, f n < f (n + 1) := by
    intro n
    rw [hf_succ]
    exact hnext_gt (f n)
  have hf_strict : StrictMono f := strictMono_nat_of_lt_succ hf_step
  let x : IncSeq := OrderEmbedding.ofStrictMono f hf_strict
  have hx_apply (n : Nat) : x n = f n := by
    rfl
  have hx_mem : ∀ n : Nat, x n ∈ X := by
    intro n
    simpa [hx_apply] using hf_mem n
  apply Exists.intro x
  apply Set.Subset.antisymm
  · exact Set.range_subset_iff.2 hx_mem
  · intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        let P : Set Nat := {m | m ∈ X ∧ m < n}
        by_cases hP : P.Nonempty
        · have hPfin : P.Finite :=
            (Set.finite_Iio n).subset (by intro m hm; exact hm.2)
          obtain ⟨p, hpPfin, hpmax⟩ := hPfin.toFinset.exists_max_image id
            (by simpa [hPfin.mem_toFinset] using hP)
          have hpP : p ∈ P := hPfin.mem_toFinset.mp hpPfin
          obtain ⟨k, hk⟩ := ih p hpP.2 hpP.1
          have hp_mem : p ∈ X := hpP.1
          have hp_lt_n : p < n := hpP.2
          have hpk : f k = p := by simpa [hx_apply] using hk
          have hnext_le : f (k + 1) ≤ n := by
            rw [hf_succ]
            apply hnext_le (f k) n
            exact ⟨hn, by simpa [hpk] using hp_lt_n⟩
          have hn_le_next : n ≤ f (k + 1) := by
            by_contra hnot
            have hnext_lt : f (k + 1) < n := Nat.lt_of_not_ge hnot
            have hnext_mem : f (k + 1) ∈ X := hf_mem (k + 1)
            have hnext_le_p : f (k + 1) ≤ p :=
              hpmax (f (k + 1))
                (hPfin.mem_toFinset.mpr ⟨hnext_mem, hnext_lt⟩)
            have hpk_lt : p < f (k + 1) := by
              simpa [hpk] using hf_step k
            exact (Nat.not_lt_of_ge hnext_le_p) hpk_lt
          have hnext_eq : f (k + 1) = n := Nat.le_antisymm hnext_le hn_le_next
          exact ⟨k + 1, by simp [hx_apply, hnext_eq]⟩
        · have hleast : ∀ m ∈ X, n ≤ m := by
            intro m hm
            by_contra hmn
            exact hP ⟨m, hm, Nat.lt_of_not_ge hmn⟩
          have hn0_le : n ≤ f 0 := hleast (f 0) (hf_mem 0)
          have hf0_le_n : f 0 ≤ n := by
            apply Nat.find_min' h_nonempty
            exact hn
          have hf0_eq : f 0 = n := Nat.le_antisymm hf0_le_n hn0_le
          exact ⟨0, by simp [hx_apply, hf0_eq]⟩
