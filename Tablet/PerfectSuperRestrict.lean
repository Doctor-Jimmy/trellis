import Tablet.PerfectSuperSequence
import Tablet.SuperSequenceRestrict

-- [TABLET NODE: PerfectSuperRestrict]
theorem PerfectSuperRestrict {Q : Type} (r : Q → Q → Prop)
    {F : Set (Finset Nat)} {X : Set Nat} (f : SuperSequence F X Q)
    (F' : Set (Finset Nat)) (Y : Set Nat) (hF' : Front F' Y)
    (hsub : F' ⊆ F) :
    PerfectSuperSequence r f →
      PerfectSuperSequence r (SuperSequenceRestrict f F' Y hF' hsub) := by
-- BODY
  intro h s t hs ht hshift
  exact h s t (hsub hs) (hsub ht) hshift
