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
  open import S4.Core.Proposition PropAtom _≟ₚ_ renaming (_≟_ to _≟p_)
  open import S4.Core.Hypothesis renaming (_≟_ to _≟h_)

  private
    variable
      n m p q : ℕ
      A B C : Proposition
      h g i : Hypothesis
      Aₕ Bₕ : (Proposition × Hypothesis)
      Δ : Context n
      Δ' : Context p
      Γ : Context m
      Γ' : Context q
      idx idx₁ idx₂ : Fin n
      idx₃ idx₄ : Fin m

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

  postulate 
  -- These seem trivially true, but very annoying to prove
    exch-lemma-4 : OnlyTrue Γ → OnlyTrue (exchange Γ idx₁ idx₂)
    exch-lemma-5 : OnlyValid Δ → OnlyValid (exchange Δ idx₁ idx₂)

  exchange-admit-Γ : ∀ idx₁ idx₂ → (Δ , Γ) ⊢ Aₕ → (Δ , (exchange Γ idx₁ idx₂)) ⊢ Aₕ
  exchange-admit-Γ idx₁ idx₂ (hyp x x₁ x₂) = hyp (exch-lemma-3 x) x₁ (exch-lemma-4 x₂)
  exchange-admit-Γ idx₁ idx₂ (⊃I D x x₁) = ⊃I (exchange-admit-Γ (suc idx₁) (suc idx₂) D) x (exch-lemma-4 x₁)
  exchange-admit-Γ idx₁ idx₂ (⊃E D D₁ x x₁) = ⊃E (exchange-admit-Γ idx₁ idx₂ D) (exchange-admit-Γ idx₁ idx₂ D₁) x (exch-lemma-4 x₁)
  exchange-admit-Γ idx₁ idx₂ (hyp* x x₁ x₂) = hyp* x x₁ (exch-lemma-4 x₂)
  exchange-admit-Γ idx₁ idx₂ (■I D x x₁) = ■I D x (exch-lemma-4 x₁)   
  exchange-admit-Γ idx₁ idx₂ (■E D D₁ x x₁) = ■E (exchange-admit-Γ idx₁ idx₂ D) (exchange-admit-Γ idx₁ idx₂ D₁) x (exch-lemma-4 x₁)

  exchange-admit-Δ : ∀ idx₁ idx₂ → (Δ , Γ) ⊢ Aₕ → ((exchange Δ idx₁ idx₂) , Γ) ⊢ Aₕ
  exchange-admit-Δ idx₁ idx₂ (hyp x x₁ x₂) = hyp x (exch-lemma-5 x₁) x₂
  exchange-admit-Δ idx₁ idx₂ (⊃I D x x₁) = ⊃I (exchange-admit-Δ idx₁ idx₂ D) (exch-lemma-5 x) x₁
  exchange-admit-Δ idx₁ idx₂ (⊃E D D₁ x x₁) = ⊃E (exchange-admit-Δ idx₁ idx₂ D) (exchange-admit-Δ idx₁ idx₂ D₁) (exch-lemma-5 x) x₁
  exchange-admit-Δ idx₁ idx₂ (hyp* x x₁ x₂) = hyp* (exch-lemma-3 x) (exch-lemma-5 x₁) x₂
  exchange-admit-Δ idx₁ idx₂ (■I D x x₁) = ■I (exchange-admit-Δ idx₁ idx₂ D) (exch-lemma-5 x) x₁
  exchange-admit-Δ idx₁ idx₂ (■E D D₁ x x₁) = ■E (exchange-admit-Δ idx₁ idx₂ D) (exchange-admit-Δ (suc idx₁) (suc idx₂) D₁) (exch-lemma-5 x) x₁

  -- Main theorem : we can simultaneously exchange in both halves of the context
  exchange-admit : ∀ idx₁ idx₂ idx₃ idx₄ → (Δ , Γ) ⊢ Aₕ → (((exchange Δ idx₁ idx₂) , Γ) ⊢ Aₕ) × ((Δ , (exchange Γ idx₃ idx₄)) ⊢ Aₕ)
  exchange-admit idx₁ idx₂ idx₃ idx₄ D = (exchange-admit-Δ idx₁ idx₂ D) , (exchange-admit-Γ idx₃ idx₄ D)

  exchange-Γ₀ : (Δ , (Γ ++ [ Aₕ ] ++ Γ')) ⊢ Bₕ → (Δ , ([ Aₕ ] ++ Γ ++ Γ')) ⊢ Bₕ
  exchange-Γ₀ {Γ = []} D = D
  exchange-Γ₀ {Γ = x ∷ Γ} {Aₕ} {Γ' = Γ'} D = {!   !}
    where
      indexOf-Aₕ : Fin (length (x ∷ Γ ++ [ Aₕ ] ++ Γ'))
      indexOf-Aₕ = inject≤ (fromℕ (length (x ∷ Γ))) (s≤s {!   !})

  -- {- Weakening -}
  -- weaken-admit-Γ : (Δ , Γ) ⊢ Aₕ → (Δ , Γ ++ Γ') ⊢ Aₕ

  -- weaken-admit-Δ : (Δ , Γ) ⊢ Aₕ → (Bₕ ∷ Δ , Γ) ⊢ Aₕ

  -- {- Contraction -}
  

  -- {- Substitution theorem -}
  -- subst-lemma-1 : OnlyTrue(Γ ++ [ Aₕ ] ++ Γ') → OnlyTrue (Γ ++ Γ')
  -- subst-lemma-1 {Γ = Vec.[]} {Γ' = Vec.[]} ot = onlyt/z
  -- subst-lemma-1 {Γ = []} {Aₕ} {Γ' = x ∷ Γ'} (onlyt/s ot) = ot
  -- subst-lemma-1 {Γ = x ∷ Γ} {Aₕ} {Γ' = []} (onlyt/s ot) = onlyt/s (subst-lemma-1 ot)
  -- subst-lemma-1 {Γ = x ∷ Γ} {Γ' = x₁ ∷ Γ'} (onlyt/s ot) = onlyt/s (subst-lemma-1 ot)


  -- subst-lemma-2 : (Δ , Γ) ⊢ Aₕ → OnlyTrue Γ 
  -- subst-lemma-3 : (Δ , Γ) ⊢ Aₕ → OnlyValid Δ
  -- subst-lemma-4 : OnlyValid (Δ ++ [ Aₕ ] ++ Δ') → OnlyValid (Δ ++ Δ')
  
  -- -- This is known as the generalised implication introduction 
  -- -- (see: https://www.researchgate.net/publication/335083302_Axiomatic_and_Dual_Systems_for_Constructive_Necessity_a_Formally_Verified_Equivalence)
  -- GEN→I : (Δ , (Γ ++ [ (A , true) ] ++ Γ' )) ⊢ (B , true) → (Δ , Γ ++ Γ') ⊢ ((A ⊃ B) , true)
  -- GEN→I {Γ = []} D = ⊃I D {!   !} {!   !}
  -- GEN→I {Γ = x ∷ Γ} D = ⊃I (exchange-Γ₀ D) {!   !} {!   !}

  -- substitution-1 : (Δ , (Γ ++ [ (A , true) ] ++ Γ' )) ⊢ (B , true) → (Δ , Γ) ⊢ ( A , true ) → (Δ , Γ ++ Γ') ⊢ (B , true)
  -- substitution-1 D1 D2 = ⊃E (GEN→I D1) (weaken-admit-Γ D2) (subst-lemma-3 D1) (subst-lemma-1 (subst-lemma-2 D1))
  -- -- substitution-1 (hyp {A = A} x x₁ x₂) D2 = ⊃E {!   !} {!   !} {!   !} {!   !} 
  -- -- substitution-1 {Γ = Γ} {A , true} {Γ' = Γ'} (⊃I {A = A₁} D1 x x₁) D2 = ⊃I (substitution-1 { Γ = (A₁ , true) ∷ Γ } D1 (weaken-admit-Γ D2)) x (subst-lemma-1 x₁)
  -- -- substitution-1 (⊃E D1 D3 x x₁) D2 = ⊃E (substitution-1 D1 D2) (substitution-1 D3 D2) x (subst-lemma-1 x₁)
  -- -- substitution-1 (hyp* x x₁ x₂) D2 = hyp* x x₁ (subst-lemma-1 x₂)
  -- -- substitution-1 (■I D1 x x₁) D2 = ■I D1 x (subst-lemma-1 x₁)                        
  -- -- substitution-1 (■E D1 D3 x x₁) D2 = ■E (substitution-1 D1 D2) (substitution-1 D3 (weaken-admit-Δ D2)) x (subst-lemma-1 x₁)     