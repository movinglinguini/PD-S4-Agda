module S4.Core.Hypothesis where

  {-
    Types of hypotheses we are allowed to make in S4.
  -}
  data Hypothesis : Set where
    -- Truth
    true : Hypothesis
    -- Validity
    valid : Hypothesis
