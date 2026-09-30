import Tablet.ContinuousRelHom
import Tablet.RightComp

-- [TABLET NODE: GBetterRel]
def GBetterRel (g : IncSeq) {A : Type} (r : A → A → Prop) : Prop :=
-- BODY
  (∀ (phi : IncSeq → A), LocallyConstant phi →
    ∃ f : IncSeq, ∃ H : ContinuousRelHom (RightComp g) r,
      ∀ x, H.toFun x = phi (IncSeqComp f x)) ∧
    ¬ Nonempty (ContinuousRelHom (RightComp g) (fun a b => ¬ r a b))
