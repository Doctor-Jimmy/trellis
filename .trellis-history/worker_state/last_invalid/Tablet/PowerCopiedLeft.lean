import Tablet.PowerIResponse
import Tablet.PowerShiftIter
import Tablet.MultiSequence

universe u

-- [TABLET NODE: PowerCopiedLeft]
noncomputable def PowerCopiedLeft {Q : Type u} (r : Q → Q → Prop)
    (h : MultiSequence (PowerQ Q)) (x : IncSeq) (n : Nat) : Nat → PowerQ Q
  := by
-- BODY
    let rec go (m : Nat) : Nat → PowerQ Q
      | 0 =>
          PowerIResponse r (h (PowerShiftIter m x))
            (h (PowerShiftIter (m + 1) x))
      | k + 1 =>
          PowerIResponse r (go m k) (go (m + 1) k)
    exact go n
