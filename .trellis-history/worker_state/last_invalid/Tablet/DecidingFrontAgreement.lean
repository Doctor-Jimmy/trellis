import Tablet.PrefixAgree
import Tablet.ProperPrefixSet

-- [TABLET NODE: DecidingFrontAgreement]
theorem DecidingFrontAgreement {x y : IncSeq} {n : Nat}
    (hp : ProperPrefixSet (Finset.image x (Finset.range n))
      (Set.range (y : Nat → Nat))) :
    PrefixAgree n x y := by
-- BODY
  classical
  rcases hp with ⟨m, hm, hset⟩
  rcases hm with ⟨j, rfl⟩
  have hset' : Finset.image x (Finset.range n) = Finset.image y (Finset.range j) := by
    ext k
    constructor
    · intro hk
      rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
      apply Finset.mem_image.mpr
      have hk' := (hset (x i)).mp (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      rcases hk'.1 with ⟨l, hl⟩
      refine ⟨l, ?_, hl⟩
      exact Finset.mem_range.mpr (y.lt_iff_lt.mp (by simpa [hl] using hk'.2))
    · intro hk
      rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
      rw [hset]
      constructor
      · exact ⟨i, rfl⟩
      · exact y.lt_iff_lt.mpr (Finset.mem_range.mp hi)
  have hcard : n = j := by
    have hxcard : (Finset.image x (Finset.range n)).card = n := by
      rw [Finset.card_image_iff.mpr]
      · exact Finset.card_range n
      · intro a ha b hb hab
        exact x.injective hab
    have hycard : (Finset.image y (Finset.range j)).card = j := by
      rw [Finset.card_image_iff.mpr]
      · exact Finset.card_range j
      · intro a ha b hb hab
        exact y.injective hab
    calc
      n = (Finset.image x (Finset.range n)).card := hxcard.symm
      _ = (Finset.image y (Finset.range j)).card := congrArg Finset.card hset'
      _ = j := hycard
  rw [← hcard] at hset'
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    cases i with
    | zero =>
      have hxi : x 0 ∈ Finset.image y (Finset.range n) := by
        rw [← hset']
        exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hi, rfl⟩
      rcases Finset.mem_image.mp hxi with ⟨j, hj, hjx⟩
      have hyi : y 0 ∈ Finset.image x (Finset.range n) := by
        rw [hset']
        exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hi, rfl⟩
      rcases Finset.mem_image.mp hyi with ⟨k, hk, hky⟩
      have hxy : x 0 ≤ y 0 := by
        by_contra hnxy
        have hlt : y 0 < x 0 := Nat.lt_of_not_ge hnxy
        rw [← hky] at hlt
        exact (Nat.not_lt_of_ge (x.monotone (Nat.zero_le k))) hlt
      have hyx : y 0 ≤ x 0 := by
        by_contra hnyx
        have hlt : x 0 < y 0 := Nat.lt_of_not_ge hnyx
        rw [← hjx] at hlt
        exact (Nat.not_lt_of_ge (y.monotone (Nat.zero_le j))) hlt
      exact Nat.le_antisymm hxy hyx
    | succ i =>
      have hxi : x (i + 1) ∈ Finset.image y (Finset.range n) := by
        rw [← hset']
        exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr hi, rfl⟩
      rcases Finset.mem_image.mp hxi with ⟨j, hj, hjx⟩
      have hyi : y (i + 1) ∈ Finset.image x (Finset.range n) := by
        rw [hset']
        exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr hi, rfl⟩
      rcases Finset.mem_image.mp hyi with ⟨k, hk, hky⟩
      have hxy : x (i + 1) ≤ y (i + 1) := by
        by_contra hnxy
        have hlt : y (i + 1) < x (i + 1) := Nat.lt_of_not_ge hnxy
        rw [← hky] at hlt
        have hki : k < i + 1 := x.lt_iff_lt.mp hlt
        have hprev_all : ∀ q, q < i + 1 → x q = y q := by
          intro q hq
          by_cases hqi : q = i
          · subst q
            exact ih i (Nat.lt_succ_self i) (Nat.lt_trans (Nat.lt_succ_self i) hi)
          · have hq_lt : q < i := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hq) hqi
            exact ih q (Nat.lt_of_lt_of_le hq_lt (Nat.le_succ _))
              (Nat.lt_trans (Nat.lt_trans hq_lt (Nat.lt_succ_self i)) hi)
        have hprev : x k = y k := hprev_all k hki
        exact (Nat.ne_of_lt (y.strictMono hki)) (hprev.symm.trans hky)
      have hyx : y (i + 1) ≤ x (i + 1) := by
        by_contra hnyx
        have hlt : x (i + 1) < y (i + 1) := Nat.lt_of_not_ge hnyx
        rw [← hjx] at hlt
        have hji : j < i + 1 := y.lt_iff_lt.mp hlt
        have hprev_all : ∀ q, q < i + 1 → x q = y q := by
          intro q hq
          by_cases hqi : q = i
          · subst q
            exact ih i (Nat.lt_succ_self i) (Nat.lt_trans (Nat.lt_succ_self i) hi)
          · have hq_lt : q < i := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hq) hqi
            exact ih q (Nat.lt_of_lt_of_le hq_lt (Nat.le_succ _))
              (Nat.lt_trans (Nat.lt_trans hq_lt (Nat.lt_succ_self i)) hi)
        have hprev : x j = y j := hprev_all j hji
        exact (Nat.ne_of_lt (x.strictMono hji)) (hprev.trans hjx)
      exact Nat.le_antisymm hxy hyx
