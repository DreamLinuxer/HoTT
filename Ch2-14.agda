{-# OPTIONS --without-K #-}

module Ch2-14 where
open import Ch2-13 public

module Semigroup where
  SemigroupStr : ∀ {ℓ} (A : Set ℓ) → Set _
  SemigroupStr A = Σ[ m ∈ (A → A → A) ] ((x y z : A) → m x (m y z) ≡ m (m x y) z)

  Semigroup : ∀ {ℓ} → Set _
  Semigroup {ℓ} = Σ[ A ∈ Set ℓ ] (SemigroupStr A)

  Semigroup→ : ∀ {ℓ} {A B : Set ℓ} → (𝒆 : A ≃ B)
             → SemigroupStr A → SemigroupStr B
  Semigroup→ {ℓ} {A} {B} 𝒆 = transport SemigroupStr (ua 𝒆)

  m : ∀ {ℓ} {A B : Set ℓ} {g : SemigroupStr A} → (A → A → A)
  m {g = g} = pr₁ g

  m' : ∀ {ℓ} {A B : Set ℓ} {𝒆 : A ≃ B} {g : SemigroupStr A} → (B → B → B)
  m' {B = B} {𝒆 = 𝒆} {g = g} = transport (λ X → (X → X → X)) (ua 𝒆) (m {B = B} {g = g})

  Assoc : ∀ {ℓ} → (x : Σ[ X ∈ Set ℓ ] (X → X → X)) → Set ℓ
  Assoc (X , m) = (x y z : X) → m x (m y z) ≡ m (m x y) z

  a' : ∀ {ℓ} {A B : Set ℓ} {𝒆 : A ≃ B} {g : SemigroupStr A} → Assoc (B , (m' {𝒆 = 𝒆} {g = g}))
  a' {A = A} {𝒆 = 𝒆} {g = m , a} = transport (λ x → Assoc x) (pairΣ≡ ((ua 𝒆) , (refl (m' {𝒆 = 𝒆} {g = m , a})))) a
