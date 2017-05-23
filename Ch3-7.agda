{-# OPTIONS --without-K #-}
module Ch3-7 where
open import Base
open import Ch3-3
open import Ch3-6
open import Level using (_⊔_; suc)

postulate
  ∥_∥ : ∀ {ℓ} (A : Set ℓ) → Set ℓ
  ∣_∣ : ∀ {ℓ} {A : Set ℓ} → A → ∥ A ∥
  inhabPath : ∀ {ℓ} {A : Set ℓ} (x y : ∥ A ∥) → x ≡ y
  rec∥-∥ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → isProp B → (f : A → B)
         → Σ[ g ∈ (∥ A ∥ → B) ] ((a : A) → g (∣ a ∣) ≡ f a)

⊤ : Set
⊤ = 𝟙

⊥ : Set
⊥ = 𝟘

_∧_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set _
P ∧ Q = P × Q

_⇒_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set _
P ⇒ Q = P → Q

_⇔_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set _
P ⇔ Q = P ≡ Q

¬'_ : ∀ {ℓ} → Set ℓ → Set _
¬' P = P → 𝟘

_∨_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set _
P ∨ Q = ∥ P + Q ∥

∀'_[_] : ∀ {ℓ ℓ'} → (A : Set ℓ) → (A  → Set ℓ') → Set _
∀' A [ P ] = (a : A) → P a

∃'_[_] : ∀ {ℓ ℓ'} → (A : Set ℓ) → (A  → Set ℓ') → Set _
∃' A [ P ] = ∥ Σ[ x ∈ A ] P x ∥
