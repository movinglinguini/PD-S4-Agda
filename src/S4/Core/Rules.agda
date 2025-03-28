open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec
open import Data.Vec.Bounded renaming ([] to []b ; _∷_ to _∷b_)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions

module S4.Core.Rules 
  (PropAtom : Set)
  (_≟ₚ_ : DecidableEquality PropAtom)
  where
  open import S4.Core.Proposition PropAtom _≟ₚ_
  open import S4.Core.Hypothesis

  data _∙_⇒_ : Hypothesis → Hypothesis → Hypothesis → Set where
    t∙t : true ∙ true ⇒ true
    v∙v : valid ∙ valid ⇒ valid

  open import CARVe.Context Proposition Hypothesis _∙_⇒_ public

  private
    variable
      n m : ℕ
      h h₁ h₂ : Hypothesis 
      Δ : Context n
      Γ : Context m
      A B C : Proposition

  -- We give ourself a way to distinguish when a part of the context contains
  -- only valid judgments.
  data OnlyValid : Context n → Set where
    onlyv/z : OnlyValid []
    onlyv/s : 
      OnlyValid Δ
      ---------------
      → OnlyValid ((A , valid) ∷ Δ)

  -- We give ourself a way to distinguish when a part of the context contains
  -- only true judgments.
  data OnlyTrue : Context n → Set where
    onlyt/z : OnlyTrue []
    onlyt/s :
      OnlyTrue Γ
      ------------------
      → OnlyTrue ((A , true) ∷ Γ)

  -- We'll need a way to strip away truth judgements from a context
  extractOnlyValid : Context n → Vec≤ (Proposition × Hypothesis) n
  extractOnlyValid [] = [] , z≤n
  extractOnlyValid (_∷_ {n} (fst , true) Δ) = ≤-cast (n≤1+n n) (extractOnlyValid Δ)
  extractOnlyValid ((fst , valid) ∷ Δ) = (fst , valid) ∷b (extractOnlyValid Δ)

  -- Proof that our function above does what we think it does
  extractOnlyValid-isValid : (Δ : Context n) → OnlyValid (toVec (extractOnlyValid Δ))
  extractOnlyValid-isValid [] = onlyv/z
  extractOnlyValid-isValid ((fst , true) ∷ Δ) = extractOnlyValid-isValid Δ
  extractOnlyValid-isValid ((fst , valid) ∷ Δ) = onlyv/s (extractOnlyValid-isValid Δ)

  {- Rules of Pfenning-Davies S4 using CARVe contexts. -}
  data _⊢_ : Context n → Proposition × Hypothesis → Set where
    {- Truth judgements -}
    hyp :
      (A , true) ∈ Δ
      ------------------------
      → Δ ⊢ (A , true)
    
    ⊃I : 
      ((A , true) ∷ Δ) ⊢ (B , true)
      ---------------------------
      → Δ ⊢ (A ⊃ B , true)

    ⊃E :
      Δ ⊢ (A ⊃ B , true)    →   Δ ⊢ (A , true)
      ------------------------------------------
      → Δ ⊢ (B , true)
    
    {- Validity judgments -}
    hyp* : 
      (B , valid) ∈ Δ
      -----------------------
      → Δ ⊢ (B , true)

    ■I : 
      Δ ⊢ (A , true)  →   OnlyValid Δ   → OnlyTrue Γ
      -----------------------
      → (Δ ++ Γ) ⊢ (■ A , true)

    ■E :
      Δ ⊢ (■ A , true)    →   ((A , valid) ∷ Δ) ⊢ (C , true)
      -------------------------------------------------------
      → Δ ⊢ (C , true)
