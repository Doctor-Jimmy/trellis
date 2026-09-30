import Tablet.LocallyConstant

-- [TABLET NODE: ContinuousRelHom]
structure ContinuousRelHom {A : Type} (s : IncSeq → IncSeq) (r : A → A → Prop) where
-- BODY
  toFun : IncSeq → A
  locallyConstant : LocallyConstant toFun
  hom : ∀ x, r (toFun x) (toFun (s x))
