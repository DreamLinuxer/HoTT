{-# OPTIONS --without-K #-}

module Ch2-14 where
open import Ch2-13 public

SemigroupStr : ∀ {ℓ} (A : Set ℓ) → Set _
SemigroupStr A = Σ[ m ∈ (A → A → A) ] ((x y z : A) → m x (m y z) ≡ m (m x y) z)

Semigroup : ∀ {ℓ ℓ'} Set ℓ
Semigroup = Σ[ A : Set ℓ ]
