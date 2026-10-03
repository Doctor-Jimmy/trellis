import Tablet.BlockSigma
import Tablet.OrbitBlockCoverage
import Tablet.IncSeq

-- [TABLET NODE: BlockSigmaEmbedding]
theorem BlockSigmaEmbedding (g : IncSeq) (k : Nat) (hk : k < g k) (f : IncSeq) :
    ∃ σ : IncSeq, ∀ l, σ l = BlockSigma g k f l := by
-- BODY
  have h_iter_strict : ∀ n, StrictMono ((g : Nat → Nat)^[n]) := by
    intro n
    induction n with
    | zero =>
        simpa using (strictMono_id : StrictMono (id : Nat → Nat))
    | succ n ih =>
        intro a b hab
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact g.strictMono (ih hab)
  have h_iter_comp : ∀ a b x,
      (g : Nat → Nat)^[a] ((g : Nat → Nat)^[b] x) =
        (g : Nat → Nat)^[a + b] x := by
    intro a b x
    exact (Function.iterate_add_apply (g : Nat → Nat) a b x).symm
  have h_iter_shift : ∀ n x,
      (g : Nat → Nat)^[n] (g x) = (g : Nat → Nat)^[n + 1] x := by
    intro n x
    rw [← h_iter_comp n 1 x]
    rfl
  have hG_step : ∀ n, OrbitPoint g k n < OrbitPoint g k (n + 1) := by
    intro n
    change (g : Nat → Nat)^[n] k < (g : Nat → Nat)^[n + 1] k
    rw [← h_iter_shift n k]
    exact h_iter_strict n hk
  have hG_strict : StrictMono (fun n => OrbitPoint g k n) :=
    strictMono_nat_of_lt_succ hG_step
  have hf_ge : ∀ n, n ≤ f n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (f.strictMono (Nat.lt_succ_self n)))
  have hg_ge : ∀ x, x ≤ g x := by
    intro x
    induction x with
    | zero => exact Nat.zero_le _
    | succ x ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (g.strictMono (Nat.lt_succ_self x)))
  have h_iter_ge : ∀ n x, x ≤ (g : Nat → Nat)^[n] x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply']
        exact (hg_ge x).trans (g.monotone (ih x))
  let sigma : Nat → Nat := fun l => BlockSigma g k f l
  have h_initial : ∀ l, l < OrbitPoint g k 0 → sigma l = l := by
    intro l hl
    dsimp [sigma]
    simp only [BlockSigma, dif_pos hl]
  have h_block : ∀ n l, OrbitBlock g k n l →
      sigma l = (g : Nat → Nat)^[f n - n] l := by
    intro n l hnl
    have hG0n : OrbitPoint g k 0 ≤ OrbitPoint g k n :=
      hG_strict.monotone (Nat.zero_le n)
    have hlG0 : ¬ l < OrbitPoint g k 0 := by
      exact not_lt_of_ge (hG0n.trans hnl.1)
    let hE : ∃ m : Nat, l < OrbitPoint g k (m + 1) := ⟨n, hnl.2⟩
    have hfind_le : Nat.find hE ≤ n := Nat.find_min' hE hnl.2
    have hfind_ge : n ≤ Nat.find hE := by
      by_contra hnot
      have hlt : Nat.find hE < n := Nat.lt_of_not_ge hnot
      have hstep : Nat.find hE + 1 ≤ n := Nat.succ_le_of_lt hlt
      have horder : OrbitPoint g k (Nat.find hE + 1) ≤ OrbitPoint g k n :=
        hG_strict.monotone hstep
      have hle : OrbitPoint g k (Nat.find hE + 1) ≤ l :=
        horder.trans hnl.1
      exact (not_lt_of_ge hle) (Nat.find_spec hE)
    have hfind : Nat.find hE = n := Nat.le_antisymm hfind_le hfind_ge
    dsimp [sigma]
    simp only [BlockSigma, dif_neg hlG0, dif_pos hE]
    rw [hfind]
  have h_sigma_lower : ∀ n l, OrbitBlock g k n l →
      OrbitPoint g k (f n) ≤ sigma l := by
    intro n l hnl
    rw [h_block n l hnl]
    have hmono : Monotone ((g : Nat → Nat)^[f n - n]) :=
      (h_iter_strict (f n - n)).monotone
    have hmap := hmono hnl.1
    have hcomp := h_iter_comp (f n - n) n k
    have hsum : f n - n + n = f n := Nat.sub_add_cancel (hf_ge n)
    calc
      OrbitPoint g k (f n) = (g : Nat → Nat)^[f n - n] (OrbitPoint g k n) := by
        change (g : Nat → Nat)^[f n] k =
          (g : Nat → Nat)^[f n - n] ((g : Nat → Nat)^[n] k)
        rw [hcomp, hsum]
      _ ≤ (g : Nat → Nat)^[f n - n] l := hmap
  have h_sigma_upper : ∀ n l, OrbitBlock g k n l →
      sigma l < OrbitPoint g k (f n + 1) := by
    intro n l hnl
    rw [h_block n l hnl]
    have hstrict := h_iter_strict (f n - n)
    have hlt := hstrict hnl.2
    have hcomp := h_iter_comp (f n - n) (n + 1) k
    have hfn := hf_ge n
    have hsum : f n - n + (n + 1) = f n + 1 := by omega
    calc
      (g : Nat → Nat)^[f n - n] l <
          (g : Nat → Nat)^[f n - n] (OrbitPoint g k (n + 1)) := hlt
      _ = OrbitPoint g k (f n + 1) := by
        change (g : Nat → Nat)^[f n - n] ((g : Nat → Nat)^[n + 1] k) =
          (g : Nat → Nat)^[f n + 1] k
        rw [hcomp, hsum]
  have hsigma_strict : StrictMono sigma := by
    intro a b hab
    obtain ha | ⟨n, hna, hna_unique⟩ := OrbitBlockCoverage g k hk a
    · obtain hb | ⟨m, hmb, hmb_unique⟩ := OrbitBlockCoverage g k hk b
      · rw [h_initial a ha, h_initial b hb]
        exact hab
      · have hG0m : OrbitPoint g k 0 ≤ OrbitPoint g k m :=
          hG_strict.monotone (Nat.zero_le m)
        have hGmf : OrbitPoint g k m ≤ OrbitPoint g k (f m) :=
          hG_strict.monotone (hf_ge m)
        have hle : OrbitPoint g k 0 ≤ sigma b :=
          hG0m.trans (hGmf.trans (h_sigma_lower m b hmb))
        exact (h_initial a ha).symm ▸ (lt_of_lt_of_le ha hle)
    · obtain hb | ⟨m, hmb, hmb_unique⟩ := OrbitBlockCoverage g k hk b
      · have hG0n : OrbitPoint g k 0 ≤ OrbitPoint g k n :=
          hG_strict.monotone (Nat.zero_le n)
        have : ¬ b < OrbitPoint g k 0 := by
          exact not_lt_of_ge (hG0n.trans (hna.1.trans (Nat.le_of_lt hab)))
        exact False.elim (this hb)
      · by_cases hnm : n = m
        · subst m
          rw [h_block n a hna, h_block n b hmb]
          exact h_iter_strict (f n - n) hab
        · have hmn : m < n ∨ n < m := lt_or_gt_of_ne (Ne.symm hnm)
          cases hmn with
          | inl hmn =>
              have hstep : m + 1 ≤ n := Nat.succ_le_of_lt hmn
              have horder : OrbitPoint g k (m + 1) ≤ OrbitPoint g k n :=
                hG_strict.monotone hstep
              have hbad : OrbitPoint g k (m + 1) ≤ b :=
                horder.trans (hna.1.trans (Nat.le_of_lt hab))
              exact False.elim ((not_lt_of_ge hbad) hmb.2)
          | inr hnm =>
              have hstep : n + 1 ≤ m := Nat.succ_le_of_lt hnm
              have hfstep : f n + 1 ≤ f m := by
                exact le_trans (Nat.succ_le_of_lt (f.strictMono (Nat.lt_succ_self n)))
                  (f.monotone hstep)
              have hGstep : OrbitPoint g k (f n + 1) ≤ OrbitPoint g k (f m) :=
                hG_strict.monotone hfstep
              exact lt_of_lt_of_le (h_sigma_upper n a hna)
                (hGstep.trans (h_sigma_lower m b hmb))
  refine ⟨OrderEmbedding.ofStrictMono sigma hsigma_strict, ?_⟩
  intro l
  rfl
