open import Data.Nat hiding (_<_; _≟_)
open import Data.Fin hiding (_+_; _≟_)
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any hiding (lookup)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.Sum

module S4.Properties 
  (PropAtom : Set)
  (_≟ₚ_ : DecidableEquality PropAtom) 
  where
  open import S4.Core.Rules PropAtom _≟ₚ_ 
  open import S4.Core.Context PropAtom _≟ₚ_
  open import S4.Core.Proposition PropAtom _≟ₚ_ renaming (_≟_ to _≟p_)
  open import S4.Core.Hypothesis renaming (_≟_ to _≟h_)

  private
    variable
      n m p q : ℕ
      t : ContextType
      A B C : Proposition
      h g i : Hypothesis
      Aₕ Bₕ : (Proposition × Hypothesis)
      Δ : HypContext n Validity
      Γ : HypContext m Truth
      idx₁ idx₂ : Fin n
      idx₃ idx₄ : Fin m
  
  postulate
    -- to prove later
    exchange-admit-Δ : ∀ idx₁ idx₂ → (Δ , Γ) ⊢ Aₕ → (exchange { t = Validity } Δ idx₁ idx₂ , Γ) ⊢ Aₕ
    exchange-admit-Γ : ∀ idx₁ idx₂ → (Δ , Γ) ⊢ Aₕ → (Δ , exchange { t = Truth } Γ idx₁ idx₂) ⊢ Aₕ