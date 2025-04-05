open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

module S4.Core.Hypothesis where

  {-
    Types of hypotheses we are allowed to make in S4.
  -}
  data Hypothesis : Set where
    -- Truth
    true : Hypothesis
    -- Validity
    valid : Hypothesis

  _≟_ : DecidableEquality Hypothesis
  true ≟ true = yes refl
  true ≟ valid = no λ ()
  valid ≟ valid = yes refl
  valid ≟ true = no (λ ())

  {-
    Binary operation on hypotheses.
    We'll need this later to instantiate our context module.
    Intuitively, this binary operation tells us that whenever we split
    a context, hypotheses stay the same up the proof tree.
    This is opposed to what we'd see in a substructural logic like linear logic,
    where linear hypotheses are transformed into irrelevant ones when they are
    "consumed".
  -}
  data _∙_⇒_ : Hypothesis → Hypothesis → Hypothesis → Set where
    t∙t : true ∙ true ⇒ true
    v∙v : valid ∙ valid ⇒ valid

