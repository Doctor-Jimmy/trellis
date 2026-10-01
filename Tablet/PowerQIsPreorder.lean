import Tablet.PowerRelTrans

universe u

-- [TABLET NODE: PowerQIsPreorder]
instance PowerQIsPreorder {Q : Type u} (r : Q → Q → Prop) [IsPreorder Q r] :
    IsPreorder (PowerQ Q) (PowerRel r) where
-- BODY
  refl := PowerRelRefl r
  trans := PowerRelTrans r
