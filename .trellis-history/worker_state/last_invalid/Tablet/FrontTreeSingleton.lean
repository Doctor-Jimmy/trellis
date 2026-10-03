import Tablet.Front
import Tablet.PrefixTree

-- [TABLET NODE: FrontTreeSingleton]
theorem FrontTreeSingleton (F : Set (Finset Nat))
    (hF : Front F Set.univ) (htriv : ∅ ∉ F) (n : Nat) :
    ({n} : Finset Nat) ∈ PrefixTree F := by
-- BODY
  classical
  have hbase : FrontBase F = (Set.univ : Set Nat) := by
    rcases hF.base_condition with h | h
    · exfalso
      apply htriv
      rw [h]
      simp
    · exact h
  let Y : Set Nat := {n} ∪ {k | n < k}
  have hYsub : Y ⊆ (Set.univ : Set Nat) := by
    intro k hk
    trivial
  have hYinf : Y.Infinite := by
    have hrange : (Set.range (fun k : Nat => n + 1 + k)).Infinite :=
      Set.infinite_range_of_injective (by
        intro a b hab
        exact Nat.add_left_cancel hab)
    apply Set.Infinite.mono ?_ hrange
    intro k hk
    rcases Set.mem_range.mp hk with ⟨m, rfl⟩
    right
    dsimp
    omega
  obtain ⟨t, htF, htY⟩ := hF.dense Y hYsub hYinf
  rcases htY with ⟨m, hmY, htm⟩
  have htne : t.Nonempty := by
    by_contra htn
    have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htn
    apply htriv
    simpa [ht0] using htF
  have hmn : m ≠ n := by
    intro hmn
    have ht0 : t = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro htne'
      obtain ⟨k, hkt⟩ := htne'
      have hkt' := (htm k).mp hkt
      have hkY : k = n ∨ n < k := by
        simpa [Y] using hkt'.1
      omega
    exact (Finset.not_nonempty_iff_eq_empty.mpr ht0) htne
  have hnm : n < m := by
    have hmY' : m = n ∨ n < m := by
      simpa [Y] using hmY
    rcases hmY' with hmn' | hnm'
    · exact (hmn hmn').elim
    · exact hnm'
  have hnt : n ∈ t := by
    apply (htm n).mpr
    exact ⟨by simp [Y], hnm⟩
  have hinit : InitialSegment ({n} : Finset Nat) t := by
    by_cases ht_single : t = {n}
    · exact Or.inl ht_single.symm
    · let d : Finset Nat := t \ {n}
      have hd : d.Nonempty := by
        apply Finset.sdiff_nonempty.mpr
        intro hsub
        apply ht_single
        apply Finset.Subset.antisymm hsub
        exact Finset.singleton_subset_iff.mpr hnt
      let q : Nat := d.min' hd
      have hq_d : q ∈ d := by
        exact Finset.min'_mem d hd
      have hq_t : q ∈ t := by
        exact (Finset.mem_sdiff.mp hq_d).1
      have hnq : n < q := by
        have hq_ne : q ≠ n := by
          intro hqn
          apply (Finset.mem_sdiff.mp hq_d).2
          simpa [hqn]
        have hqY := (htm q).mp hq_t
        have hqY' : q = n ∨ n < q := by
          simpa [Y] using hqY.1
        rcases hqY' with hqn | hnq
        · exact (hq_ne hqn).elim
        · exact hnq
      have hfilter : ({n} : Finset Nat) = t.filter (fun k => k < q) := by
        apply Finset.ext
        intro k
        constructor
        · intro hk
          have hkn : k = n := by simpa using hk
          subst k
          exact Finset.mem_filter.mpr ⟨hnt, hnq⟩
        · intro hk
          have hk' := Finset.mem_filter.mp hk
          have hkY := (htm k).mp hk'.1
          have hkY' : k = n ∨ n < k := by
            simpa [Y] using hkY.1
          rcases hkY' with hkn | hnk
          · simpa [hkn]
          · have hk_d : k ∈ d := by
              exact Finset.mem_sdiff.mpr ⟨hk'.1, by
                simpa using (Nat.ne_of_gt hnk)⟩
            exact False.elim
              ((Nat.not_lt_of_ge (Finset.min'_le d k hk_d)) hk'.2)
      exact Or.inr ⟨q, hq_t, hfilter⟩
  exact ⟨t, htF, hinit⟩
