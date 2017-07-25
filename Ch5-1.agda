{-# OPTIONS --without-K #-}
module Ch5-1 where
open import Base

-- Theorem 5.1.1
uniq[ΠℕE] : ∀ {ℓ} {E : ℕ → Set ℓ} (f g : (x : ℕ) → E x)
          → (ez : E 0) (es : (n : ℕ) → E n → E (succ n))
          → f 0 ≡ ez → g 0 ≡ ez
          → ((n : ℕ) → f (succ n) ≡ es n (f n))
          → ((n : ℕ) → g (succ n) ≡ es n (g n))
          → f ≡ g
uniq[ΠℕE] f g ez es f0 g0 fs gs =
          funext (indℕ (λ x → f x ≡ g x) (f0 ▪ g0 ⁻¹) (λ n p → fs n ▪ ap (es n) p ▪ gs n ⁻¹))
