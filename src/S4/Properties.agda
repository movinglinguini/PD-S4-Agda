open import Data.Nat hiding (_<_; _≟_)
open import Data.Fin hiding (_+_; _≟_)
open import Data.Vec
open import Data.Vec.Bounded hiding (_∷_)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any hiding (lookup)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Nullary

module S4.Properties 
  (PropAtom : Set)
  (_≟ₚ_ : DecidableEquality PropAtom) 
  where
  open import S4.Core.Rules PropAtom _≟ₚ_ 
  open import S4.Core.Proposition PropAtom _≟ₚ_ renaming (_≟_ to _≟p_)
  open import S4.Core.Hypothesis renaming (_≟_ to _≟h_)

  private
    variable
      n : ℕ
      A B C : Proposition
      h g i : Hypothesis
      Aₕ Bₕ : (Proposition × Hypothesis)
      Δ Δ' : Context n
      idx idx₁ idx₂ : Fin n

  -- A refl between a pair means a pair of refls for their constituents.
  ≡-pair⇒≡ : ∀ { A B : Proposition } → (A ≡ B) × (h ≡ g) → ((A , h)) ≡ (B , g) 
  ≡-pair⇒≡ (refl , refl) = refl

  -- Building up decidable equality between tagged propositions
  _≟_ : DecidableEquality (Proposition × Hypothesis)
  Aₕ ≟ Bₕ with (proj₁ Aₕ) ≟p (proj₁ Bₕ) | (proj₂ Aₕ) ≟h (proj₂ Bₕ)
  ... | no ¬p | _ = no (λ x → ¬p (cong proj₁ x))
  ... | _ | no ¬p = no (λ x → ¬p (cong proj₂ x))
  ... | yes p₁ | yes p₂ = yes (≡-pair⇒≡ (p₁ , p₂))

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

  exch-lemma-2 : ∀ idx → ((A , h) ∈ Δ) × (¬ ((A , h) ≡ (lookup Δ idx))) → (A , h) ∈ (replace Δ idx Bₕ)
  exch-lemma-2 zero (here px , snd) = contradiction px snd
  exch-lemma-2 (suc idx) (here px , snd) = here px
  exch-lemma-2 zero (there fst , snd) = there fst
  exch-lemma-2 (suc idx) (there fst , snd) = there (exch-lemma-2 idx (fst , snd))

  exch-lemma-3 : Aₕ ∈ Δ → Aₕ ∈ (exchange Δ idx₁ idx₂)
  exch-lemma-3 {idx₁ = zero} {zero} (here px) = here px
  exch-lemma-3 {Δ = Δ} {idx₁ = suc {n} idx₁} {zero} (here refl) = there (exch-lemma-1 idx₁)
  exch-lemma-3 {idx₁ = zero} {suc idx₂} (here refl) = there (exch-lemma-1 idx₂)
  exch-lemma-3 {idx₁ = suc idx₁} {suc idx₂} (here px) = here px
  exch-lemma-3 {idx₁ = zero} {zero} (there mem) = there mem
  exch-lemma-3 {Aₕ} {idx₁ = zero} {suc idx₂} (there {xs = xs} mem) with Aₕ ≟ (lookup xs idx₂)
  exch-lemma-3 {Aₕ} {_} {_} {zero} {suc idx₂} (there {xs = _} mem) | no ¬p = there (exch-lemma-2 idx₂ (mem , ¬p))
  ... | yes p = here p
  exch-lemma-3 {Aₕ} {idx₁ = suc idx₁} {zero} (there {x = x} {xs} mem) with Aₕ ≟ (lookup xs idx₁)
  ... | no ¬p = there (exch-lemma-2 idx₁ (mem , ¬p))
  ... | yes p = here p
  exch-lemma-3 {idx₁ = suc idx₁} {suc idx₂} (there mem) = there (exch-lemma-3 mem)

  exchange-admit : ∀ idx₁ idx₂ → Δ ⊢ Aₕ → (exchange Δ idx₁ idx₂) ⊢ Aₕ
  exchange-admit idx₁ idx₂ (hyp x) = hyp (exch-lemma-3 x)
  exchange-admit idx₁ idx₂ (⊃I D) = {!   !}
  exchange-admit idx₁ idx₂ (⊃E D D₁) = {!   !}
  exchange-admit idx₁ idx₂ (hyp* x) = hyp* (exch-lemma-3 x)
  exchange-admit idx₁ idx₂ (■I {Δ = Δ} D v t) = ■I (exchange-admit {!   !} {!   !} {!   !}) {!   !} {!   !}
  exchange-admit idx₁ idx₂ (■E D D₁) = {!   !}