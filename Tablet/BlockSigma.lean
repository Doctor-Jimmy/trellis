import Tablet.OrbitPoint

-- [TABLET NODE: BlockSigma]
noncomputable def BlockSigma (g : IncSeq) (k : Nat) (f : IncSeq) (l : Nat) : Nat :=
-- BODY
  by
    classical
    exact if h0 : l < OrbitPoint g k 0 then l
      else if h : ∃ n, l < OrbitPoint g k (n + 1) then
        ((g : Nat → Nat)^[f (Nat.find h) - Nat.find h]) l
      else l
