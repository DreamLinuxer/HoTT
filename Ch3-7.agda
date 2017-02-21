{-# OPTIONS --without-K #-}
module Ch3-7 where
open import Base
open import Ch3-3
open import Ch3-6
open import Level using (_⊔_; suc)

data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ∥ A ∥

postulate
  inhabPath : ∀ {ℓ} {A : Set ℓ} (x y : ∥ A ∥) → x ≡ y
  rec∥-∥ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → isProp B → (f : A → B)
         → Σ[ g ∈ (∥ A ∥ → B) ] ((a : A) → g (∣ a ∣) ≡ f a)

⊤ : Set
⊤ = isProp 𝟙

⊥ : Set
⊥ = isProp 𝟘

_∧_ : ∀ {ℓ ℓ'} {P : Set ℓ} {Q : Set ℓ'} → isProp P → isProp Q → Set (ℓ ⊔ ℓ')
_∧_ {P = P} {Q = Q} _ _ = isProp (P × Q)

_⇒_ : ∀ {ℓ ℓ'} {P : Set ℓ} {Q : Set ℓ'} → isProp P → isProp Q → Set (ℓ ⊔ ℓ')
_⇒_ {P = P} {Q = Q} _ _ = isProp (P → Q)

¬'_ : ∀ {ℓ} {P : Set ℓ} → isProp P → Set ℓ
¬'_ {P = P} _ = isProp (P → 𝟘)

_∨_ : ∀ {ℓ ℓ'} {P : Set ℓ} {Q : Set ℓ'} → isProp P → isProp Q → Set (ℓ ⊔ ℓ')
_∨_ {P = P} {Q = Q} _ _ = ∥ P + Q ∥
