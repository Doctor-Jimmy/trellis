import Tablet.Front
import Tablet.IncSeq

-- [TABLET NODE: FrontPrefix]
def FrontPrefix (F : Set (Finset Nat)) (s : Finset Nat) (x : IncSeq) : Prop :=
-- BODY
  s ∈ F ∧ ProperPrefixSet s (Set.range (x : Nat → Nat))
