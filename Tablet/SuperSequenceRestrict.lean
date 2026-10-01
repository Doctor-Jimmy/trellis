import Tablet.SuperSequence

-- [TABLET NODE: SuperSequenceRestrict]
def SuperSequenceRestrict {E : Type} {F : Set (Finset Nat)} {X : Set Nat}
    (f : SuperSequence F X E) (F' : Set (Finset Nat)) (Y : Set Nat)
    (hF' : Front F' Y) (hsub : F' ⊆ F) : SuperSequence F' Y E :=
-- BODY
  { front := hF'
    value := fun s => f.value ⟨s.1, hsub s.2⟩ }
