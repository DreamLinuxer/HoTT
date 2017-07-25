-- Formalization of https://arxiv.org/abs/1504.05531
-- Homotopy-initial algebras in type theory
{-# OPTIONS --without-K #-}
module hinitiality-3 where
open import Base
open import Ch3-3
open import Ch3-6
open import hinitiality-2

-- Definition 3.1
isind : ∀ {ℓ ℓ'} → (A : Bip {ℓ}) → Set _
isind {ℓ} {ℓ'} A = (E : FibBip {ℓ' = ℓ'} A) → BipSec A E

BipInd : ∀ {ℓ ℓ'} → Set _
BipInd {ℓ} {ℓ'} = Σ[ A ∈ Bip {ℓ} ] isind {ℓ' = ℓ'} A

-- Proposition 3.2
elim : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
     → (x : pr₁ A) (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A))) → E x
elim {A = (A , a₀ , a₁)} AisInd E x e₀ e₁ = pr₁ (AisInd (E , e₀ , e₁)) x

comp₀ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
      → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
      → elim AisInd E (pr₁ (pr₂ A)) e₀ e₁ ≡ e₀
comp₀ {A = (A , a₀ , a₁)} AisInd E e₀ e₁ = pr₁ (pr₂ (AisInd (E , e₀ , e₁)))

comp₁ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
      → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
      → elim AisInd E (pr₂ (pr₂ A)) e₀ e₁ ≡ e₁
comp₁ {A = (A , a₀ , a₁)} AisInd E e₀ e₁ = pr₂ (pr₂ (AisInd (E , e₀ , e₁)))

-- Proposition 3.3
η : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
  → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
  → (f : (x : pr₁ A) → E x) → f (pr₁ (pr₂ A)) ≡ e₀ → f (pr₂ (pr₂ A)) ≡ e₁
  → (x : pr₁ A) → (f x) ≡ elim AisInd E x e₀ e₁
η {A = (A , a₀ , a₁)} AisInd E e₀ e₁ f f₀ f₁ x = elim AisInd F x p₀ p₁
  where
  F : A → Set _
  F x = f x ≡ elim AisInd E x e₀ e₁

  p₀ = f₀ ▪ comp₀ AisInd E e₀ e₁ ⁻¹
  p₁ = f₁ ▪ comp₁ AisInd E e₀ e₁ ⁻¹

η₀ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
   → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
   → (f : (x : pr₁ A) → E x) → (f₀ : f (pr₁ (pr₂ A)) ≡ e₀) → (f₁ : f (pr₂ (pr₂ A)) ≡ e₁)
   → η AisInd E e₀ e₁ f f₀ f₁ (pr₁ (pr₂ A)) ▪ comp₀ AisInd E e₀ e₁ ≡ f₀
η₀ {A = (A , a₀ , a₁)} AisInd E e₀ e₁ f f₀ f₁ = ap (λ x → x ▪ comp₀ AisInd E e₀ e₁) (comp₀ AisInd F p₀ p₁)
                                              ▪ assoc▪ _ _ _ ⁻¹
                                              ▪ ap (λ x → f₀ ▪ x) (p⁻¹▪p≡refly _)
                                              ▪ unit-right _ ⁻¹
  where
  F : A → Set _
  F x = f x ≡ elim AisInd E x e₀ e₁

  p₀ = f₀ ▪ comp₀ AisInd E e₀ e₁ ⁻¹
  p₁ = f₁ ▪ comp₁ AisInd E e₀ e₁ ⁻¹

η₁ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
   → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
   → (f : (x : pr₁ A) → E x) → (f₀ : f (pr₁ (pr₂ A)) ≡ e₀) → (f₁ : f (pr₂ (pr₂ A)) ≡ e₁)
   → η AisInd E e₀ e₁ f f₀ f₁ (pr₂ (pr₂ A)) ▪ comp₁ AisInd E e₀ e₁ ≡ f₁
η₁ {A = (A , a₀ , a₁)} AisInd E e₀ e₁ f f₀ f₁ = ap (λ x → x ▪ comp₁ AisInd E e₀ e₁) (comp₁ AisInd F p₀ p₁)
                                              ▪ assoc▪ _ _ _ ⁻¹
                                              ▪ ap (λ x → f₁ ▪ x) (p⁻¹▪p≡refly _)
                                              ▪ unit-right _ ⁻¹
  where
  F : A → Set _
  F x = f x ≡ elim AisInd E x e₀ e₁

  p₀ = f₀ ▪ comp₀ AisInd E e₀ e₁ ⁻¹
  p₁ = f₁ ▪ comp₁ AisInd E e₀ e₁ ⁻¹

-- Proposition 3.4
isind→isPropBipSec : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A)
                   → (E : FibBip {ℓ' = ℓ'} A)
                   → (f g : BipSec A E) → f ≡ g
isind→isPropBipSec {A = (A , a₀ , a₁)} AisInd (E , e₀ , e₁) (f , f₀ , f₁) (g , g₀ , g₁) =
  ≃← (BipSec≃ _ _) ((λ x → ηf x ▪ ηg x ⁻¹) , η₀' , η₁')
  where
  ηf = η AisInd E e₀ e₁ f f₀ f₁
  ηg = η AisInd E e₀ e₁ g g₀ g₁
  ηf₀ = η₀ AisInd E e₀ e₁ f f₀ f₁
  ηf₁ = η₁ AisInd E e₀ e₁ f f₀ f₁
  ηg₀ = η₀ AisInd E e₀ e₁ g g₀ g₁
  ηg₁ = η₁ AisInd E e₀ e₁ g g₀ g₁
  com₀ = comp₀ AisInd E e₀ e₁
  com₁ = comp₁ AisInd E e₀ e₁

  η₀' : f₀ ≡ ηf a₀ ▪ ηg a₀ ⁻¹ ▪ g₀
  η₀' = l-cancel {r = ηf a₀ ⁻¹} _ _
        (ηf a₀ ⁻¹ ▪ f₀
      ≡⟨ ap (λ x → ηf a₀ ⁻¹ ▪ x) (ηf₀ ⁻¹) ⟩
         ηf a₀ ⁻¹ ▪ (ηf a₀ ▪ com₀)
      ≡⟨ assoc▪ _ _ _ ▪ ap (λ x → x ▪ com₀) (p⁻¹▪p≡refly _) ⟩
         refl _ ▪ com₀
      ≡⟨ ap (λ x → x ▪ com₀) (p⁻¹▪p≡refly _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ▪ ap (λ x → ηg a₀ ⁻¹ ▪ x) ηg₀ ⟩
         ηg a₀ ⁻¹ ▪ g₀
      ≡⟨ unit-left (ηg a₀ ⁻¹ ▪ g₀) ▪ assoc▪ _ _ _ ▪ ap (λ x → x  ▪ ηg a₀ ⁻¹ ▪ g₀) (p⁻¹▪p≡refly _ ⁻¹) ⟩
         ηf a₀ ⁻¹ ▪ ηf a₀ ▪ ηg a₀ ⁻¹ ▪ g₀
      ≡⟨ ap (λ x → x ▪ g₀) (assoc▪ _ _ _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ⟩
         ηf a₀ ⁻¹ ▪ (ηf a₀ ▪ ηg a₀ ⁻¹ ▪ g₀) ∎)

  η₁' : f₁ ≡ ηf a₁ ▪ ηg a₁ ⁻¹ ▪ g₁
  η₁' = l-cancel {r = ηf a₁ ⁻¹} _ _
        (ηf a₁ ⁻¹ ▪ f₁
      ≡⟨ ap (λ x → ηf a₁ ⁻¹ ▪ x) (ηf₁ ⁻¹) ⟩
         ηf a₁ ⁻¹ ▪ (ηf a₁ ▪ com₁)
      ≡⟨ assoc▪ _ _ _ ▪ ap (λ x → x ▪ com₁) (p⁻¹▪p≡refly _) ⟩
         refl _ ▪ com₁
      ≡⟨ ap (λ x → x ▪ com₁) (p⁻¹▪p≡refly _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ▪ ap (λ x → ηg a₁ ⁻¹ ▪ x) ηg₁ ⟩
         ηg a₁ ⁻¹ ▪ g₁
      ≡⟨ unit-left (ηg a₁ ⁻¹ ▪ g₁) ▪ assoc▪ _ _ _ ▪ ap (λ x → x  ▪ ηg a₁ ⁻¹ ▪ g₁) (p⁻¹▪p≡refly _ ⁻¹) ⟩
         ηf a₁ ⁻¹ ▪ ηf a₁ ▪ ηg a₁ ⁻¹ ▪ g₁
      ≡⟨ ap (λ x → x ▪ g₁) (assoc▪ _ _ _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ⟩
         ηf a₁ ⁻¹ ▪ (ηf a₁ ▪ ηg a₁ ⁻¹ ▪ g₁) ∎)

isindIsProp : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → isProp (isind {ℓ' = ℓ'} A)
isindIsProp {ℓ} {ℓ'} {A} AisInd _ = ΠisProp (isind→isPropBipSec AisInd) _ _

