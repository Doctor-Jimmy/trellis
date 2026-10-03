import Tablet.ContMor
import Tablet.RightComp
import Tablet.ShiftMap
import Tablet.FirstMovedPoint
import Tablet.OrbitEmbedding

-- [TABLET NODE: RmapLemma]
theorem RmapLemma (g : IncSeq) (hg : g ≠ IncSeqId) :
    ContMor (RightComp g) ShiftMap := by
-- BODY
  obtain ⟨k, hk, hkmin⟩ := FirstMovedPoint g hg
  obtain ⟨G, hG⟩ := OrbitEmbedding g k hk
  refine ⟨{ toFun := fun f => IncSeqComp f G, continuous := ?_, commutes := ?_ }⟩
  · intro f n
    cases n with
    | zero =>
        refine ⟨0, ?_⟩
        intro h hfh i hi
        exact False.elim (Nat.not_lt_zero i hi)
    | succ n =>
        refine ⟨G n + 1, ?_⟩
        intro h hfh i hi
        have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi
        have hGi : G i < G n + 1 :=
          lt_of_le_of_lt (G.monotone hi_le) (Nat.lt_succ_self (G n))
        simpa [IncSeqComp] using hfh (G i) hGi
  · intro f
    apply DFunLike.ext _ _
    intro n
    have hstep : g (G n) = G (n + 1) := by
      rw [hG n, hG (n + 1)]
      change g ((g : Nat → Nat)^[n] k) = (g : Nat → Nat)^[n + 1] k
      rw [Function.iterate_succ_apply']
    change f (g (G n)) = f (G (n + 1))
    rw [hstep]
