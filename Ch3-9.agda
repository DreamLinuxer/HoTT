{-# OPTIONS --without-K #-}
module Ch3-9 where
open import Base
open import Ch3-3
open import Ch3-7

-- Lemma 3.9.1
P≃∥P∥ : ∀ {ℓ} (P : Set ℓ) → isProp P → P ≃ ∥ P ∥
P≃∥P∥ P PisProp = P≃Q PisProp inhabPath ∣_∣ (λ p → rec∥-∥ PisProp id p)

-- Corollary 3.9.2
UC : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ')
   → ((x : A) → isProp (P x))
   → ((x : A) → ∥ P x ∥)
   → ((x : A) → P x)
UC P PxisProp ∥Px∥ x with P≃∥P∥ (P x) (PxisProp x)
UC P PxisProp ∥Px∥ x | f , eq with isequiv→qinv eq
UC P PxisProp ∥Px∥ x | f , eq | g , α , β = g (∥Px∥ x)
