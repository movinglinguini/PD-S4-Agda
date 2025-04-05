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
  
  private
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

  {- Rules of Pfenning-Davies S4 using CARVe contexts. -}
  data _⊢_ : (Context n × Context m) → Proposition × Hypothesis → Set where
    {- Truth judgements -}
    hyp :
      (A , true) ∈ Γ
      ------------------------
      → (Δ , Γ) ⊢ (A , true)
    
    ⊃I : 
      ( Δ , ((A , true) ∷ Γ)) ⊢ (B , true)
      ---------------------------
      → (Δ , Γ) ⊢ (A ⊃ B , true)

    ⊃E :
      (Δ , Γ) ⊢ (A ⊃ B , true)    →   (Δ , Γ) ⊢ (A , true)
      ------------------------------------------
      → (Δ , Γ) ⊢ (B , true)
    
    {- Validity judgments -}
    hyp* : 
      (B , valid) ∈ Δ
      -----------------------
      → (Δ , Γ) ⊢ (B , true)

    ■I : 
      (Δ , []) ⊢ (A , true)
      -----------------------
      → (Δ , Γ) ⊢ (■ A , true)

    ■E :
      (Δ , Γ) ⊢ (■ A , true)    →   (((A , valid) ∷ Δ) , Γ) ⊢ (C , true)
      -------------------------------------------------------
      → (Δ , Γ) ⊢ (C , true)
