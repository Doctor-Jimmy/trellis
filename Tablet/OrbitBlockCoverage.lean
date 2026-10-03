import Tablet.OrbitBlock
import Tablet.OrbitEmbedding
import Tablet.OrbitUnbounded

-- [TABLET NODE: OrbitBlockCoverage]
theorem OrbitBlockCoverage (g : IncSeq) (k : Nat) (hk : k < g k) :
    ∀ l : Nat,
      l < OrbitPoint g k 0 ∨ ∃! n : Nat, OrbitBlock g k n l := by
-- BODY
  obtain ⟨G, hG⟩ := OrbitEmbedding g k hk
  intro l
  by_cases hl : l < G 0
  · left
    rw [← hG 0]
    exact hl
  · right
    have hG0 : G 0 ≤ l := Nat.le_of_not_gt hl
    obtain ⟨r, hr⟩ := OrbitUnbounded g k hk l
    have hS : ∃ n : Nat, l < G (n + 1) := by
      cases r with
      | zero => exact False.elim (hl (by simpa [hG 0] using hr))
      | succ m =>
          refine ⟨m, ?_⟩
          simpa [Nat.succ_eq_add_one, hG (m + 1)] using hr
    have hn_upper : l < G (Nat.find hS + 1) := Nat.find_spec hS
    have hn_lower : G (Nat.find hS) ≤ l := by
      cases hN : Nat.find hS with
      | zero => simpa [hN] using hG0
      | succ t =>
          have hlt : t < Nat.find hS := by
            rw [hN]
            exact Nat.lt_succ_self t
          have hnot : ¬ l < G (t + 1) := Nat.find_min hS hlt
          have hle : G (t + 1) ≤ l := Nat.le_of_not_gt hnot
          simpa [hN, Nat.succ_eq_add_one] using hle
    refine ⟨Nat.find hS, ?_, ?_⟩
    · change OrbitPoint g k (Nat.find hS) ≤ l ∧
        l < OrbitPoint g k (Nat.find hS + 1)
      rw [← hG (Nat.find hS), ← hG (Nat.find hS + 1)]
      exact ⟨hn_lower, hn_upper⟩
    · intro m hm
      have hm' := hm
      dsimp [OrbitBlock] at hm'
      rw [← hG m, ← hG (m + 1)] at hm'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hmn | hnm
      · have hstep : m + 1 ≤ Nat.find hS := Nat.succ_le_of_lt hmn
        have horder : G (m + 1) ≤ G (Nat.find hS) := G.monotone hstep
        have hupper : l < G (m + 1) := hm'.2
        have hle : G (m + 1) ≤ l := horder.trans hn_lower
        exact (not_lt_of_ge hle) hupper
      · have hstep : Nat.find hS + 1 ≤ m := Nat.succ_le_of_lt hnm
        have horder : G (Nat.find hS + 1) ≤ G m := G.monotone hstep
        have hupper : l < G (Nat.find hS + 1) := hn_upper
        have hle : G (Nat.find hS + 1) ≤ l := horder.trans hm'.1
        exact (not_lt_of_ge hle) hupper
