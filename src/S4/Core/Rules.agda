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
  open import S4.Core.Context PropAtom _≟ₚ_
  
  private
    variable
      n m : ℕ
      h h₁ h₂ : Hypothesis 
      Δ : HypContext n Validity
      Γ : HypContext m Truth
      A B C : Proposition

  {- Rules of Pfenning-Davies S4 using CARVe contexts. -}
  data _⊢_ : (HypContext n Validity) × (HypContext m Truth) → Proposition × Hypothesis → Set where
    {- Truth judgements -}
    hyp :
      ------------------------
      (Δ , (to/truth (A , true) prop/true) ∷ʰ Γ) ⊢ (A , true)
    
    ⊃I : 
      ( Δ , (to/truth (A , true) prop/true ∷ʰ Γ)) ⊢ (B , true)
      ---------------------------
      → (Δ , Γ) ⊢ (A ⊃ B , true)

    ⊃E :
      (Δ , Γ) ⊢ (A ⊃ B , true)    →   (Δ , Γ) ⊢ (A , true)
      ------------------------------------------
      → (Δ , Γ) ⊢ (B , true)
    
    {- Validity judgments -}
    hyp* : 
      -----------------------
      ((to/validity (B , valid) prop/valid) ∷ʰ Δ , Γ) ⊢ (B , true)

    ■I : 
      (Δ , ([] , onlyt/z)) ⊢ (A , true)
      -----------------------
      → (Δ , Γ) ⊢ (■ A , true)

    ■E :
      (Δ , Γ) ⊢ (■ A , true)    →   ((to/validity (A , valid) prop/valid ∷ʰ Δ) , Γ) ⊢ (C , true)
      -------------------------------------------------------
      → (Δ , Γ) ⊢ (C , true)
