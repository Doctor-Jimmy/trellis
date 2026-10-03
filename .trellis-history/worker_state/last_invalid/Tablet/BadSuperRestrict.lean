import Tablet.BadSuperSequence
import Tablet.SuperSequenceRestrict

-- [TABLET NODE: BadSuperRestrict]
theorem BadSuperRestrict {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q)
    (F' : Set (Finset Nat)) (Y : Set Nat) (hF' : Front F' Y)
    (hsub : F' ⊆ F) :
    BadSuperSequence r f →
      BadSuperSequence r (SuperSequenceRestrict f F' Y hF' hsub) := by
-- BODY
  intro hbad s t hs ht hshift
  exact hbad s t (hsub hs) (hsub ht) hshift
