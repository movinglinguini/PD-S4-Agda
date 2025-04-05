open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any hiding (lookup)
open import Data.Product
open import Relation.Binary.Definitions
open import Data.Sum
open import Relation.Binary.PropositionalEquality

module S4.Core.Context 
  (PropAtom : Set)
  (_≟ₚ_ : DecidableEquality PropAtom)
  where

  open import S4.Core.Hypothesis
  open import S4.Core.Proposition PropAtom _≟ₚ_
  open import CARVe.Context Proposition Hypothesis _∙_⇒_

  private
    variable
      n : ℕ
      Δ Γ : Context n
      A : Proposition
      Aₕ : TaggedProposition

  {- 
    We define two kinds of contexts: validity and truth.
    We'll define each of these as pairs of a context with a proof
    that the context only contains hypotheses of a given type.
    So, a validity context should only contain validity hyps. 
  -}
  data Valid : TaggedProposition → Set where
    prop/valid : Valid (A , valid)
  
  data True : TaggedProposition → Set where
    prop/true : True (A , true)

  data OnlyValid : Context n → Set where
    onlyv/z : OnlyValid []
    onlyv/s : 
      OnlyValid Δ → Valid Aₕ
      ---------------
      → OnlyValid (Aₕ ∷ Δ)

  data OnlyTrue : Context n → Set where
    onlyt/z : OnlyTrue []
    onlyt/s :
      OnlyTrue Γ → True Aₕ
      ------------------
      → OnlyTrue (Aₕ ∷ Γ)

  data ContextType : Set where
    Validity : ContextType
    Truth : ContextType

  data PropDestination : TaggedProposition → ContextType → Set where
    to/validity : 
      (Aₕ : TaggedProposition) → (isValid : Valid Aₕ)
      → PropDestination Aₕ Validity

    to/truth :
      (Aₕ : TaggedProposition) → (isTrue : True Aₕ)
      → PropDestination Aₕ Truth


  -- A hypothesis context is a context paramaterized by the type of context
  -- it's supposed to be. So a validity context is one that is paired with
  -- a context 
  HypContext : ℕ → ContextType → Set
  HypContext n Validity = Σ (Context n) (λ Δ → OnlyValid Δ)
  HypContext n Truth = Σ (Context n) (λ Δ → OnlyTrue Δ)

  {- Operations on these contexts -}
  -- Appending to a context. A tagged proposition is bound for a matching context.
  -- For example, a truth proposition is bound for a truth context.
  _∷ʰ_ : ∀ { t : ContextType } → PropDestination Aₕ t → HypContext n t → HypContext (suc n) t
  to/validity Aₕ isValid ∷ʰ Δ = Aₕ ∷ Δ .proj₁ , onlyv/s (Δ .proj₂) isValid
  to/truth Aₕ isTrue ∷ʰ Δ = Aₕ ∷ Δ .proj₁ , onlyt/s (Δ .proj₂) isTrue

  -- Context membership
  _∈ʰ_ : ∀ { t : ContextType } → PropDestination Aₕ t → HypContext n t → Set
  to/validity Aₕ isValid ∈ʰ (Δ , only-valid) = Aₕ ∈ Δ
  to/truth Aₕ isTrue ∈ʰ (Γ , only-true) = Aₕ ∈ Γ

  -- Context exchange
  private
    replace : Context n → (idx : Fin n) → (Proposition × Hypothesis) → Context n
    replace (x ∷ Δ) zero A = A ∷ Δ
    replace (x ∷ Δ) (suc idx) A = x ∷ (replace Δ idx A)

    lookup-∈ : ∀ { idx : Fin n } → (Δ : Context n) → (lookup Δ idx) ∈ Δ
    lookup-∈ {idx = zero} (x ∷ Δ) = here refl
    lookup-∈ {idx = suc idx} (x ∷ Δ) = there (lookup-∈ Δ)

    ∈-Δ⇒valid : OnlyValid Δ → Aₕ ∈ Δ → Valid Aₕ
    ∈-Δ⇒valid (onlyv/s only-valid x) (here refl) = x
    ∈-Δ⇒valid (onlyv/s only-valid x) (there mem) = ∈-Δ⇒valid only-valid mem

    ∈-Δ⇒true : OnlyTrue Γ → Aₕ ∈ Γ → True Aₕ
    ∈-Δ⇒true (onlyt/s only-true x) (here refl) = x
    ∈-Δ⇒true (onlyt/s only-true x) (there mem) = ∈-Δ⇒true only-true mem

    valid-replace⇒valid : ∀ { idx : Fin n } → OnlyValid Δ → Valid Aₕ → OnlyValid (replace Δ idx Aₕ)
    valid-replace⇒valid {idx = zero} (onlyv/s only-valid x) prop/valid = onlyv/s only-valid prop/valid
    valid-replace⇒valid {idx = suc idx} (onlyv/s only-valid x) prop/valid = onlyv/s (valid-replace⇒valid only-valid prop/valid) x  

    true-replace⇒true : ∀ { idx : Fin n } → OnlyTrue Γ → True Aₕ → OnlyTrue (replace Γ idx Aₕ)
    true-replace⇒true {idx = zero} (onlyt/s only-true x) true-prop = onlyt/s only-true true-prop
    true-replace⇒true {idx = suc idx} (onlyt/s only-true x) true-prop = onlyt/s (true-replace⇒true only-true true-prop) x
  

  private
    variable
      t : ContextType
  {-
    Exhange within a context.  
  -}
  exchange : HypContext n t → Fin n → Fin n → HypContext n t
  exchange {n} {t = Validity} (Δ , only-valid) idx₁ idx₂ = Δ'' , Δ''-valid
    where
      Bₕ : TaggedProposition
      Bₕ = lookup Δ idx₁

      Cₕ : TaggedProposition
      Cₕ = lookup Δ idx₂

      Bₕ-valid : Valid Bₕ
      Bₕ-valid = ∈-Δ⇒valid only-valid (lookup-∈ Δ)

      Cₕ-valid : Valid Cₕ
      Cₕ-valid = ∈-Δ⇒valid only-valid (lookup-∈ Δ)

      Δ' = replace Δ idx₁ Cₕ
      Δ'-valid : OnlyValid Δ'
      Δ'-valid = valid-replace⇒valid only-valid Cₕ-valid

      Δ'' = replace Δ' idx₂ Bₕ
      Δ''-valid : OnlyValid Δ''
      Δ''-valid = valid-replace⇒valid Δ'-valid Bₕ-valid

  exchange {t = Truth} (Γ , only-true) idx₁ idx₂ = Γ'' , Γ''-true
    where
      Bₕ : TaggedProposition
      Bₕ = lookup Γ idx₁

      Cₕ : TaggedProposition
      Cₕ = lookup Γ idx₂

      Bₕ-true : True Bₕ
      Bₕ-true = ∈-Δ⇒true only-true (lookup-∈ Γ)

      Cₕ-true : True Cₕ
      Cₕ-true = ∈-Δ⇒true only-true (lookup-∈ Γ)

      Γ' = replace Γ idx₁ Cₕ
      Γ'-true : OnlyTrue Γ'
      Γ'-true = true-replace⇒true only-true Cₕ-true

      Γ'' = replace Γ' idx₂ Bₕ
      Γ''-true : OnlyTrue Γ''
      Γ''-true = true-replace⇒true Γ'-true Bₕ-true
  
  private
    ∈-replace⇒∈ : ∀ { Δ : Context n } idx → Aₕ ∈ Δ → Aₕ ∈ (replace Δ idx Aₕ)
    ∈-replace⇒∈ zero (here refl) = here refl
    ∈-replace⇒∈ zero (there mem) = here refl
    ∈-replace⇒∈ (suc idx) (here refl) = here refl
    ∈-replace⇒∈ (suc idx) (there mem) = there (∈-replace⇒∈ idx mem) 

  {- Properties of exchange -}
  postulate
    -- I'll prove this later. It's a lot of cases 
    ∈⇒exchange-∈ : ∀ idx₁ idx₂ { P : PropDestination Aₕ t } { Ψ : HypContext n t } 
      → P ∈ʰ Ψ 
      → P ∈ʰ (exchange Ψ idx₁ idx₂)
