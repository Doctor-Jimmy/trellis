import Tablet.OrbitBlock
import Tablet.OrbitEmbedding
import Tablet.OrbitUnbounded

-- [TABLET NODE: OrbitBlockCoverage]
theorem OrbitBlockCoverage (g : IncSeq) (k : Nat) (hk : k < g k) :
    ∀ l : Nat,
      l < OrbitPoint g k 0 ∨ ∃! n : Nat, OrbitBlock g k n l := by
-- BODY
  sorry
