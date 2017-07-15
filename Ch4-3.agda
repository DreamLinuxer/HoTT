{-# OPTIONS --without-K #-}
module Ch4-3 where
open import Base
open import Ch3-3
open import Ch3-11
open import Ch4-2
open import Ex3

biinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set _
biinv f = linv f × rinv f

biinv→qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
           → biinv f → qinv f
biinv→qinv {f = f} ((g , η) , (h , ε)) =
           let γ : g ~ h
               γ x = ap g (ε x ⁻¹) ▪ η (h x)
           in  h , (ε , (λ x → γ (f x) ⁻¹ ▪ η x))

qinv→biinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
           → qinv f → biinv f
qinv→biinv (g , η , ε) = (g , ε) , (g , η)

-- Theorem 4.3.2
biinvIsProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
            → isProp (biinv f)
biinvIsProp f = ≃← Ex3-5.isPropA≃[A→isContrA] contr
  where
  contr : biinv f → isContr (biinv f)
  contr binv with biinv→qinv binv
  ... | qinv = ×isContr (qinv→isContr[linv] f qinv) (qinv→isContr[rinv] f qinv)

-- Corollary 4.3.3
biinv≃ishae : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
            → biinv f ≃ ishae f
biinv≃ishae f = P≃Q (biinvIsProp f) (ishaeIsProp f) (qinv→ishae ∘ biinv→qinv) (qinv→biinv ∘ ishae→qinv)
