import Tablet.Preamble

-- [TABLET NODE: InitialSegment]
def InitialSegment (u v : Finset Nat) : Prop :=
-- BODY
  u = v ∨ ∃ n ∈ v, u = v.filter (fun k => k < n)
