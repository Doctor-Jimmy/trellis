import Tablet.BlockSigma
import Tablet.OrbitBlockCoverage
import Tablet.PrefixAgree

-- [TABLET NODE: BlockSigmaContinuous]
theorem BlockSigmaContinuous (g : IncSeq) (k : Nat) (hk : k < g k) :
    ∀ f : IncSeq, ∀ n : Nat, ∃ m : Nat, ∀ h : IncSeq,
      PrefixAgree m f h → ∀ l < n, BlockSigma g k h l = BlockSigma g k f l := by
-- BODY
  obtain ⟨G, hG⟩ := OrbitEmbedding g k hk
  intro f n
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      intro h hfh l hl
      exact (Nat.not_lt_zero l hl).elim
  | succ n ih =>
      rcases ih with ⟨m, hm⟩
      by_cases hinit : n < OrbitPoint g k 0
      · refine ⟨m, ?_⟩
        intro h hfh l hlsucc
        by_cases hln : l < n
        · exact hm h hfh l hln
        · have hle : l ≤ n := Nat.le_of_lt_succ hlsucc
          have hge : n ≤ l := Nat.le_of_not_gt hln
          have h_eq : l = n := Nat.le_antisymm hle hge
          subst l
          simp only [BlockSigma, dif_pos hinit]
      · rcases OrbitBlockCoverage g k hk n with hleft | ⟨q, hq, _⟩
        · exact (hinit hleft).elim
        · refine ⟨max m (q + 1), ?_⟩
          intro h hfh l hlsucc
          by_cases hln : l < n
          · have hprefix : PrefixAgree m f h := by
              intro i hi
              exact hfh i (lt_of_lt_of_le hi (Nat.le_max_left _ _))
            exact hm h hprefix l hln
          · have hle : l ≤ n := Nat.le_of_lt_succ hlsucc
            have hge : n ≤ l := Nat.le_of_not_gt hln
            have h_eq : l = n := Nat.le_antisymm hle hge
            subst l
            have hq_lower : OrbitPoint g k q ≤ n := hq.1
            let hE : ∃ i : Nat, n < OrbitPoint g k (i + 1) := ⟨q, hq.2⟩
            have hfind_le : Nat.find hE ≤ q := Nat.find_min' hE hq.2
            have hfind_lt : Nat.find hE < max m (q + 1) := by
              exact lt_of_le_of_lt hfind_le
                (lt_of_lt_of_le (Nat.lt_succ_self q) (Nat.le_max_right _ _))
            have hzero_le_q : OrbitPoint g k 0 ≤ OrbitPoint g k q := by
              rw [← hG 0, ← hG q]
              exact G.monotone (Nat.zero_le q)
            have hnot0 : ¬ n < OrbitPoint g k 0 :=
              Nat.not_lt.mpr (hzero_le_q.trans hq_lower)
            have hblock_value : ∀ x : IncSeq,
                BlockSigma g k x n =
                  ((g : Nat → Nat)^[x (Nat.find hE) - Nat.find hE]) n := by
              intro x
              simp only [BlockSigma, dif_neg hnot0, dif_pos hE]
            have hindex : f (Nat.find hE) = h (Nat.find hE) :=
              hfh (Nat.find hE) hfind_lt
            rw [hblock_value h, hblock_value f, hindex]
