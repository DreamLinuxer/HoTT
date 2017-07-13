{-# OPTIONS --without-K #-}
module Ex3 where

--Ex 3.1
module Ex3-1 where
  open import Base
  open import Ch3-1
  open import Ch3-8
  open import Level

  isSetA×[A≃B]→BisSet : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → isSet A → A ≃ B → isSet B
  isSetA×[A≃B]→BisSet {ℓ} {ℓ'} {A} {B} AisSet eq = AisSet→l[A]isSet L[B]isSet
    where
    L[A]isSet : isSet (Lift {ℓ = ℓ ⊔ ℓ'} A)
    L[A]isSet = AisSet→L[A]isSet AisSet

    L[A]≃L[B] : (Lift {ℓ = ℓ ⊔ ℓ'} A) ≃ (Lift {ℓ = ℓ ⊔ ℓ'} B)
    L[A]≃L[B] = tran≃ (sym≃ A≃L[A]) (tran≃ eq A≃L[A])

    L[B]isSet : isSet (Lift {ℓ = ℓ ⊔ ℓ'} B)
    L[B]isSet = transport isSet (ua L[A]≃L[B]) L[A]isSet
    
