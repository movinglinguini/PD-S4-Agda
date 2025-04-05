open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≟_)
open import Data.Product

module S4.Core.Proposition 
  (PropAtom : Set)
  (_≟ₚ_ : DecidableEquality PropAtom)
  where

  infix 50 _⊃_ 
  infix 60 ■_

  data Proposition : Set where
    `_ : PropAtom → Proposition
    _⊃_ : Proposition → Proposition → Proposition
    ■_ : Proposition → Proposition

  private
    variable
      x₁ x₂ : PropAtom
      A₁ A₂ B₁ B₂ A B : Proposition

  {-
    Building up decidable equality between propositions 
  -}
  ≡⇒≡ : (` x₁) ≡ (` x₂) → x₁ ≡ x₂
  ≡⇒≡ refl = refl

  ≡⇒⊃≡ : A₁ ≡ B₁ → A₂ ≡ B₂ → A₁ ⊃ A₂ ≡ B₁ ⊃ B₂
  ≡⇒⊃≡ refl refl = refl

  ⊃≡⇒≡ : A₁ ⊃ A₂ ≡ B₁ ⊃ B₂ → (A₁ ≡ B₁) × (A₂ ≡ B₂)
  ⊃≡⇒≡ refl = refl , refl

  ■≡⇒≡ : ■ A ≡ ■ B → A ≡ B
  ■≡⇒≡ refl = refl

  _≟_ : DecidableEquality Proposition
  (` x₁) ≟ (` x₂) with x₁ ≟ₚ x₂
  ... | no ¬a = no (λ x → ¬a (≡⇒≡ x))
  ... | yes a = yes (cong `_ a)
  (` x) ≟ (B ⊃ B₁) = no (λ ())
  (` x) ≟ (■ B) = no λ ()
  (A ⊃ A₁) ≟ (` x) = no (λ ())
  (A₁ ⊃ A₂) ≟ (B₁ ⊃ B₂) with A₁ ≟ B₁ | A₂ ≟ B₂
  ... | no ¬a | _ = no λ x → ¬a (proj₁ (⊃≡⇒≡ x))
  ... | _ | no ¬a = no λ x → ¬a (proj₂ (⊃≡⇒≡ x))
  ... | yes a | yes a₁ = yes (≡⇒⊃≡ a a₁)
  (A ⊃ A₁) ≟ (■ B) = no (λ ())
  (■ A) ≟ (` x) = no (λ ())
  (■ A) ≟ (B ⊃ B₁) = no (λ ())
  (■ A) ≟ (■ B) with A ≟ B
  ... | no ¬p = no (λ x → ¬p (■≡⇒≡ x))
  ... | yes p = yes (cong ■_ p)

