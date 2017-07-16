{-# OPTIONS --without-K #-}
module Ch4-4 where
open import Base
open import Ch3-3
open import Ch3-6
open import Ch3-11
open import Ch4-2
open import Ch4-3

-- Definition 4.4.1
isContract : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set _
isContract {B = B} f = (y : B) → isContr (fib f y)

-- Theorem 4.4.3
isContr→ishae : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
              → isContract f → ishae f
isContr→ishae {f = f} P = g , ε
                        , ≃← (rcoh≃ f g ε) (λ x → pr₂ (P (f x)) (g (f x) , ε (f x)) ⁻¹
                                                ▪ pr₂ (P (f x)) (x , refl (f x)))
              where
              g = (λ y → pr₁ (pr₁ (P y)))
              ε = (λ y → pr₂ (pr₁ (P y)))

-- Lemma 4.4.4
isContractisProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
                  → isProp (isContract f)
isContractisProp f = ΠisProp (λ _ → isContrAisProp)

-- Theorem 4.4.5
isContract≃ishae : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
                 → isContract f ≃ ishae f 
isContract≃ishae f = P≃Q (isContractisProp f) (ishaeIsProp f) isContr→ishae hae→isContr[fib]

isContract≃isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
                   → isContract f ≃ isequiv f
isContract≃isequiv f = isContract≃ishae f ▪≃ biinv≃ishae f ⁻¹≃

-- Corollary 4.4.6
[B→isequiv]→isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
                    → (B → isequiv f) → isequiv f
[B→isequiv]→isequiv f e = (≃← (biinv≃ishae f) ∘ isContr→ishae)
                          (λ y → hae→isContr[fib] (≃→ (biinv≃ishae f) (e y)) y)
