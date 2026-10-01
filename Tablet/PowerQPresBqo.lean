import Tablet.Bqo
import Tablet.PowerQReflection

universe u

-- [TABLET NODE: PowerQPresBqo]
theorem PowerQPresBqo {Q : Type u} (r : Q → Q → Prop)
    [IsPreorder Q r] :
    Bqo r → Bqo (PowerRel r) := by
-- BODY
  sorry
