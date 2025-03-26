open import Data.Nat hiding (_<_)
open import Data.Fin hiding (_+_; cast)
open import Data.Vec
open import Data.Vec.Bounded hiding (_∷_)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any hiding (lookup)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions

module S4.Properties 
  (PropAtom : Set)
  (_≟ₚ_ : DecidableEquality PropAtom) 
  where
  open import S4.Core.Rules PropAtom _≟ₚ_ 
  open import S4.Core.Proposition PropAtom _≟ₚ_ 
  open import S4.Core.Hypothesis

  private
    variable
      n : ℕ
      A B C : Proposition
      h g i : Hypothesis
      Δ : Context n
      idx idx₁ idx₂ : Fin n

  {- Admittance of exchange -}
  private
    replace : Context n → (idx : Fin n) → (Proposition × Hypothesis) → Context n
    replace (x ∷ Δ) zero A = A ∷ Δ
    replace (x ∷ Δ) (suc idx) A = x ∷ (replace Δ idx A)

  -- Definition of exchange. We do an inplace exchange of two arbitrary elements
  -- in a context.
  exchange : Context n → (idx₁ : Fin n) → (idx₂ : Fin n) → Context n
  exchange {n} Δ idx₁ idx₂ =
    let a = lookup Δ idx₁
    in let Δ' = replace Δ idx₁ (lookup Δ idx₂)
    in replace Δ' idx₂ a

  exch-lemma-1 : ∀ idx → (A , h) ∈ (replace Δ idx (A , h))
  exch-lemma-1 {Δ = x ∷ Δ} zero = here refl
  exch-lemma-1 {Δ = x ∷ Δ} (suc idx) = there (exch-lemma-1 idx)
  
  exch-lemma-3 : (A , h) ∈ Δ → (A , h) ∈ (exchange Δ idx₁ idx₂)
  exch-lemma-3 {idx₁ = zero} {zero} (here px) = here px
  exch-lemma-3 {Δ = Δ} {idx₁ = suc {n} idx₁} {zero} (here refl) = there (exch-lemma-1 idx₁)
  exch-lemma-3 {idx₁ = zero} {suc idx₂} (here refl) = there (exch-lemma-1 idx₂)
  exch-lemma-3 {idx₁ = suc idx₁} {suc idx₂} (here px) = here px
  exch-lemma-3 {idx₁ = zero} {zero} (there mem) = there mem
  exch-lemma-3 {idx₁ = zero} {suc idx₂} (there mem) = {!   !}
  exch-lemma-3 {idx₁ = suc idx₁} {zero} (there mem) = {!   !}
  exch-lemma-3 {idx₁ = suc idx₁} {suc idx₂} (there mem) = {!   !}

  exchange-admit : ∀ { idx₁ idx₂ } → Δ ⊢ (A , h) → (exchange Δ idx₁ idx₂) ⊢ (A , h)
  exchange-admit (hyp x) = hyp (exch-lemma-3 x)
  exchange-admit (⊃I D) = ⊃I (exchange-admit D)
  exchange-admit (⊃E D D₁) = ⊃E (exchange-admit D) (exchange-admit D₁)
  exchange-admit (hyp* x) = hyp* (exch-lemma-3 x)
  exchange-admit (■I D) = ■I {!   !}        
  exchange-admit (■E D D₁) = ■E (exchange-admit D) (exchange-admit D₁)    