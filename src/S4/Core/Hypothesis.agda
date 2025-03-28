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
