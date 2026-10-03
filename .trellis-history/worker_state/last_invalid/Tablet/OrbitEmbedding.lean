import Tablet.OrbitPoint
import Tablet.IncSeq

-- [TABLET NODE: OrbitEmbedding]
theorem OrbitEmbedding (g : IncSeq) (k : Nat) (hk : k < g k) :
    ∃ G : IncSeq, ∀ n, G n = OrbitPoint g k n := by
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
  have h_iter_shift : ∀ n x,
      (g : Nat → Nat)^[n] (g x) = (g : Nat → Nat)^[n + 1] x := by
    intro n x
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  have h_step : ∀ n, OrbitPoint g k n < OrbitPoint g k (n + 1) := by
    intro n
    change (g : Nat → Nat)^[n] k < (g : Nat → Nat)^[n + 1] k
    rw [← h_iter_shift n k]
    exact h_iter_strict n hk
  have h_strict : StrictMono (fun n => OrbitPoint g k n) :=
    strictMono_nat_of_lt_succ h_step
  let G : IncSeq := OrderEmbedding.ofStrictMono (fun n => OrbitPoint g k n) h_strict
  refine ⟨G, ?_⟩
  intro n
  rfl
