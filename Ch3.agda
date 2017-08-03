{-# OPTIONS --without-K #-}
module Ch3 where
open import Base
open import Ch3-1 public
open import Ch3-2 public
open import Ch3-3 public
open import Ch3-4 public
open import Ch3-6 public
open import Ch3-7 public
open import Ch3-8 public
open import Ch3-9 public
open import Ch3-11 public

≃isProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → isProp A → isProp B
≃isProp (f , eq) AisProp x y with isequiv→qinv eq
≃isProp (f , eq) AisProp x y | g , ε , η = ε x ⁻¹ ▪ ap f (AisProp (g x) (g y)) ▪ ε y
