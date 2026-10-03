import Tablet.BlockSigma
import Tablet.OrbitBlockCoverage
import Tablet.RightComp
import Tablet.SuccSeq

-- [TABLET NODE: BlockSigmaIntertwines]
theorem BlockSigmaIntertwines (g : IncSeq) (k : Nat) (hk : k < g k)
    (hfix : ∀ j < k, g j = j) :
    ∀ f : IncSeq, ∀ l : Nat,
      BlockSigma g k (RightComp SuccSeq f) l = BlockSigma g k f (g l) := by
-- BODY
  intro f l
  obtain hinit | ⟨n, hblock, huniq⟩ := OrbitBlockCoverage g k hk l
  · have hlk : l < k := by
      simpa [OrbitPoint] using hinit
    have hgl : g l = l := hfix l hlk
    have hinit_g : g l < OrbitPoint g k 0 := by
      simpa [hgl] using hinit
    simp only [BlockSigma, dif_pos hinit, dif_pos hinit_g]
    exact hgl.symm
  · obtain ⟨G, hG⟩ := OrbitEmbedding g k hk
    have hG0n : OrbitPoint g k 0 ≤ OrbitPoint g k n := by
      rw [← hG 0, ← hG n]
      exact G.monotone (Nat.zero_le n)
    have hG0l : OrbitPoint g k 0 ≤ l := hG0n.trans hblock.1
    have hGsucc : ∀ m, OrbitPoint g k (m + 1) = g (OrbitPoint g k m) := by
      intro m
      change (g : Nat → Nat)^[m + 1] k = g ((g : Nat → Nat)^[m] k)
      rw [Function.iterate_succ_apply']
    have hleft : OrbitPoint g k (n + 1) ≤ g l := by
      rw [hGsucc n]
      exact g.monotone hblock.1
    have hright : g l < OrbitPoint g k ((n + 1) + 1) := by
      rw [hGsucc (n + 1)]
      exact g.strictMono hblock.2
    have hBlockValue : ∀ (x : IncSeq) (m y : Nat),
        OrbitBlock g k m y →
          BlockSigma g k x y = (g : Nat → Nat)^[x m - m] y := by
      intro x m y hym
      have hG0m : OrbitPoint g k 0 ≤ OrbitPoint g k m := by
        rw [← hG 0, ← hG m]
        exact G.monotone (Nat.zero_le m)
      have hG0y : OrbitPoint g k 0 ≤ y := hG0m.trans hym.1
      have hy0 : ¬ y < OrbitPoint g k 0 := not_lt_of_ge hG0y
      let hE : ∃ q : Nat, y < OrbitPoint g k (q + 1) := ⟨m, hym.2⟩
      have hfind_le : Nat.find hE ≤ m := Nat.find_min' hE hym.2
      have hfind_ge : m ≤ Nat.find hE := by
        by_contra hnot
        have hlt : Nat.find hE < m := Nat.lt_of_not_ge hnot
        have hstep : Nat.find hE + 1 ≤ m := Nat.succ_le_of_lt hlt
        have horder : OrbitPoint g k (Nat.find hE + 1) ≤ OrbitPoint g k m := by
          rw [← hG (Nat.find hE + 1), ← hG m]
          exact G.monotone hstep
        have hle : OrbitPoint g k (Nat.find hE + 1) ≤ y := horder.trans hym.1
        exact (not_lt_of_ge hle) (Nat.find_spec hE)
      have hfind : Nat.find hE = m := Nat.le_antisymm hfind_le hfind_ge
      simp only [BlockSigma, dif_neg hy0, dif_pos hE]
      rw [hfind]
    have hleft_val := hBlockValue (RightComp SuccSeq f) n l hblock
    have hright_val := hBlockValue f (n + 1) (g l) ⟨hleft, hright⟩
    have hshift : (RightComp SuccSeq f) n = f (n + 1) := by
      rfl
    rw [hleft_val, hright_val, hshift]
    have hf_ge : ∀ m : Nat, m ≤ f m := by
      intro m
      induction m with
      | zero => exact Nat.zero_le _
      | succ m ih =>
          exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (f.strictMono (Nat.lt_succ_self m)))
    have hsub : f (n + 1) - (n + 1) + 1 = f (n + 1) - n := by
      have hf := hf_ge (n + 1)
      omega
    have h_iter_shift : ∀ a x,
        (g : Nat → Nat)^[a] (g x) = (g : Nat → Nat)^[a + 1] x := by
      intro a x
      induction a with
      | zero => simp
      | succ a ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rw [h_iter_shift (f (n + 1) - (n + 1)) l, hsub]
