import Tablet.IncSeq

-- [TABLET NODE: IncSeqPointwiseLe]
theorem IncSeqPointwiseLe : ∀ (f : IncSeq) (n : Nat), n ≤ f n := by
-- BODY
  intro f n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hlt : f n < f (Nat.succ n) :=
        f.strictMono (Nat.lt_succ_self n)
      exact le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt hlt)
