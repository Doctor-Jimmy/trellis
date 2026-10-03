import Tablet.Bqo
import Tablet.PowerQReflection

universe u

-- [TABLET NODE: PowerQPresBqo]
theorem PowerQPresBqo {Q : Type u} (r : Q → Q → Prop)
    [IsPreorder Q r] :
    Bqo r → Bqo (PowerRel r) := by
-- BODY
  intro hr h hloc hbad
  obtain ⟨g, hgloc, hgbad, _⟩ := PowerQReflection r h hloc hbad
  exact hr g hgloc hgbad
