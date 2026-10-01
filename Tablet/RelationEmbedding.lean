import Tablet.Preamble

-- [TABLET NODE: RelationEmbedding]
def RelationEmbedding {A B : Type} (r : A → A → Prop) (s : B → B → Prop)
    (e : A → B) : Prop :=
-- BODY
  Function.Injective e ∧ ∀ a b, r a b ↔ s (e a) (e b)

