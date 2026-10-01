import Tablet.FrontTreeWellFounded

-- [TABLET NODE: FrontTreeOrderedExtension]
theorem FrontTreeOrderedExtension (F : Set (Finset Nat))
    (hF : Front F Set.univ) (s : Finset Nat)
    (hs : s ∈ PrefixTree F) (hsF : s ∉ F) (n : Nat)
    (hn : ProperInitialSegment s (insert n s)) :
    insert n s ∈ PrefixTree F := by
-- BODY
  sorry
