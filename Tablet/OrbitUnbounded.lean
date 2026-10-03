import Tablet.OrbitPoint
import Tablet.OrbitEmbedding

-- [TABLET NODE: OrbitUnbounded]
theorem OrbitUnbounded (g : IncSeq) (k : Nat) (hk : k < g k) :
    ∀ l : Nat, ∃ n : Nat, l < OrbitPoint g k n := by
-- BODY
  obtain ⟨G, hG⟩ := OrbitEmbedding g k hk
  intro l
  have h_lower : ∀ n : Nat, n ≤ G n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (G.strictMono (Nat.lt_succ_self n)))
  refine ⟨l + 1, ?_⟩
  rw [← hG (l + 1)]
  exact lt_of_lt_of_le (Nat.lt_succ_self l) (h_lower (l + 1))
