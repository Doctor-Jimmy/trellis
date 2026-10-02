import Tablet.DecidingFront
import Tablet.FinitePrefixExtension

universe u

-- [TABLET NODE: DecidingValue]
theorem DecidingValue {E : Type u} (h : MultiSequence E)
    (hlc : LocallyConstant h) :
    ∃ v : DecidingFrontSet h → E,
      ∀ (s : DecidingFrontSet h) (x : IncSeq),
        ProperPrefixSet s.1 (Set.range (x : Nat → Nat)) → v s = h x := by
-- BODY
  classical
  choose y hy using (fun s : DecidingFrontSet h => FinitePrefixExtension s.1)
  refine ⟨fun s => h (y s), ?_⟩
  intro s x hx
  exact s.2.1 (y s) x (hy s) hx
