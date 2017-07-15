{-# OPTIONS --without-K #-}
module Ch4-6 where
open import Base
open import Ch3-3
open import Ch3-6
open import Ch3-7
open import Ch3-11
open import Ch4-2
open import Ch4-3
open import Ch4-4

-- Definition 4.6.1
surjective : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set _
surjective {B = B} f = (b : B) → ∥ fib f b ∥

embedding : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set _
embedding {A = A} f = (x y : A) → isequiv {A = x ≡ y} (ap f)

-- Theorem 4.6.3
iseq→surj×embed : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
                → isequiv f → surjective f × embedding f
iseq→surj×embed {f = f} eq = (λ b → ∣ pr₁ ((hae→isContr[fib] ∘ ≃→ (biinv≃ishae f)) eq b) ∣)
                           , (λ x y → ap≡ _ eq)

surj×embed→iseq : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
                → surjective f × embedding f → isequiv f
surj×embed→iseq {B = B} {f = f} (surj , embed) = (≃← (biinv≃ishae f) ∘ isContr→ishae) isContrf
  where
  isContrf : isContract f
  isContrf b = pr₁ (rec∥-∥ isContrAisProp (λ x → x , (λ y → γ x y))) (surj b)
    where
    γ : (x y : fib f b) → x ≡ y
    γ (x , p) (y , q) with isequiv→qinv (embed x y)
    ... | ap⁻¹ , η , ε = pairΣ≡ (r , transport[x↦fx≡gx] f _ r p ▪ t)
      where
      r = ap⁻¹ (p ▪ q ⁻¹)
      
      s : p ≡ ap f r ▪ q
      s = r-cancel p (ap f r ▪ q) ( η (p ▪ q ⁻¹) ⁻¹
                                  ▪ unit-right _
                                  ▪ ap (λ x₁ → ap f r ▪ x₁) (p▪p⁻¹≡reflx q ⁻¹)
                                  ▪ assoc▪ _ _ _)
                                   
      t : ap f r ⁻¹ ▪ p ▪ ap (λ v → b) r ≡ q
      t = ap (λ x → ap f r ⁻¹ ▪ x ▪ ap (λ v → b) r) s
        ▪ ap (λ x → x ▪ ap (λ v → b) r) (assoc▪ _ _ _)
        ▪ ap (λ x₁ → x₁ ▪ q ▪ ap (λ v → b) r) (p⁻¹▪p≡refly _)
        ▪ ap (λ x → refl (f y) ▪ q ▪ x) (apconst _)
        ▪ unit-right _ ⁻¹
        ▪ unit-left _ ⁻¹

-- Corollary 4.6.4
iseq≃surj×embed : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
                → isequiv f ≃ surjective f × embedding f
iseq≃surj×embed = P≃Q (biinvIsProp _) (×isProp (λ f g → funext (λ x → inhabPath _ _))
                                               (λ e₁ e₂ → funext (λ x → funext (λ y → biinvIsProp _ _ _))))
                      iseq→surj×embed surj×embed→iseq
