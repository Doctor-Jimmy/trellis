import Tablet.Preamble

-- [TABLET NODE: RelationEmbedding]
def RelationEmbedding {A B : Type} (r : A → A → Prop) (s : B → B → Prop)
    (e : A → B) : Prop :=
-- BODY
  ∃ E : @RelEmbedding A B r s, (E : A → B) = e
