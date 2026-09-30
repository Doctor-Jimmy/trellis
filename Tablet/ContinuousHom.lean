import Tablet.BaireContinuous

-- [TABLET NODE: ContinuousHom]
structure ContinuousHom (r s : IncSeq → IncSeq) where
-- BODY
  toFun : IncSeq → IncSeq
  continuous : BaireContinuous toFun
  commutes : ∀ f, toFun (r f) = s (toFun f)
