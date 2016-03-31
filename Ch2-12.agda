{-# OPTIONS --without-K #-}

module Ch2-12 {ℓ} {ℓ'} where
open import Level using (Lift)
open import Ch2-11 public

--2.12

code : {A : Set ℓ} {B : Set ℓ'} {a₀ : A} → A + B → Set ℓ
code {a₀ = a₀} (inl a) = a₀ ≡ a
code {a₀ = a₀} (inr b) = Lift 𝟘

encode : {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (p : inl a₀ ≡ x) → code {a₀ = a₀} x
encode {A} {B} {a₀} x p = {!!}
