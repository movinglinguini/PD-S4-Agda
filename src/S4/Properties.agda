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
    {- Exchange -}
    exchange-admit-Δ : ∀ idx₁ idx₂ → (Δ , Γ) ⊢ Aₕ → (exchange { t = Validity } Δ idx₁ idx₂ , Γ) ⊢ Aₕ
    exchange-admit-Γ : ∀ idx₁ idx₂ → (Δ , Γ) ⊢ Aₕ → (Δ , exchange { t = Truth } Γ idx₁ idx₂) ⊢ Aₕ

    {- Weakening -}
    weaken-Γ : ∀ { Γ : HypContext m Truth } → (Δ , ([] , onlyt/z)) ⊢ Aₕ → (Δ , Γ) ⊢ Aₕ

    {- Substitution Lemmas -}
    subst-1 : 
      (Δ , (to/truth (A , true) prop/true) ∷ʰ Γ) ⊢ Bₕ
      → (Δ , Γ) ⊢ (A , true)
      → (Δ , Γ) ⊢ Bₕ

    subst-2 : 
      ((to/validity (A , valid) prop/valid) ∷ʰ Δ , Γ) ⊢ Bₕ 
      → (Δ , ([] , onlyt/z )) ⊢ (A , true)
      → (Δ , Γ) ⊢ Bₕ

  -- Detachment lemma. Got the idea for this from https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/dualcontext-sequent-calculus-for-the-constructive-modal-logic-s4/6C2B03C7BCCD1DECC924E48BA3A2E43D
  detach-⊃ : (Δ , (to/truth (A , true) prop/true) ∷ʰ Γ) ⊢ (B , true) → (Δ , Γ) ⊢ (A ⊃ B , true)
  detach-⊃ (hyp x) = ⊃I (hyp x)
  detach-⊃ (⊃I D) = ⊃I (detach-⊃ D)
  detach-⊃ (⊃E D D₁) = ⊃I (⊃E D D₁)
  detach-⊃ (hyp* x) = ⊃I (hyp* x)
  detach-⊃ (■I D) = ⊃I (■I D)
  detach-⊃ (■E D D₁) = ⊃I (■E D D₁)
  -- detach-⊃ (∧I D D₁) = ⊃I (∧I D D₁)
  -- detach-⊃ (∧E₁ D) = ⊃I (∧E₁ D)
  -- detach-⊃ (∧E₂ D) = ⊃I (∧E₂ D)
  -- detach-⊃ (∨I₁ D) = ⊃I (∨I₁ D)
  -- detach-⊃ (∨I₂ D) = ⊃I (∨I₂ D)

  -- Generalized implication lemma for S4
  gen-⊃ : (Δ , Γ) ⊢ (A , true) → (Δ , Γ) ⊢ (A ⊃ B , true) → (Δ , Γ) ⊢ (B , true) 
  gen-⊃ (hyp x) D2 = ⊃E D2 (hyp x)
  gen-⊃ (⊃I D1) D2 = ⊃E D2 (detach-⊃ D1)
  gen-⊃ (⊃E D1 D3) D2 = ⊃E D2 (⊃E D1 D3)
  gen-⊃ (hyp* x) D2 = ⊃E D2 (hyp* x)
  gen-⊃ (■I D1) D2 = ⊃E D2 (■I D1)
  gen-⊃ (■E D1 D3) D2 = ⊃E D2 (■E D1 D3)
  -- gen-⊃ (∧I D1 D3) D2 = ⊃E D2 (∧I D1 D3)
  -- gen-⊃ (∧E₁ D1) D2 = ⊃E D2 (∧E₁ D1)
  -- gen-⊃ (∧E₂ D1) D2 = ⊃E D2 (∧E₂ D1)
  -- gen-⊃ (∨I₁ D1) D2 = ⊃E D2 (∨I₁ D1)
  -- gen-⊃ (∨I₂ D1) D2 = ⊃E D2 (∨I₂ D1)

   