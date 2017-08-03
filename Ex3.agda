{-# OPTIONS --without-K #-}
module Ex3 where

--Ex 3.1
module Ex3-1 where
  open import Base
  open import Ch3-1
  open import Ch3-8
  open import Level

  ≃isSet : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → isSet A → A ≃ B → isSet B
  ≃isSet AisSet (f , eq) b _ (refl _) q with isequiv→qinv eq
  ... | (g , ε , η) = α _ _ (ap (ap f) (AisSet (g b) (g b) (ap g (refl _)) (ap g q)) ▪ ap∘ g f b b q)
    where
    α : (r s : b ≡ b) → ap (f ∘ g) r ≡ ap (f ∘ g) s → r ≡ s
    α r s γ = apid b b r ⁻¹ ▪ ≃→ (idtoeqv (ap (λ h → ap h r ≡ ap h s) (funext ε))) γ ▪ apid b b s

  -- isSetA×[A≃B]→BisSet : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → isSet A → A ≃ B → isSet B
  -- isSetA×[A≃B]→BisSet {ℓ} {ℓ'} {A} {B} AisSet eq = AisSet→l[A]isSet L[B]isSet
  --   where
  --   L[A]isSet : isSet (Lift {ℓ = ℓ ⊔ ℓ'} A)
  --   L[A]isSet = AisSet→L[A]isSet AisSet

  --   L[A]≃L[B] : (Lift {ℓ = ℓ ⊔ ℓ'} A) ≃ (Lift {ℓ = ℓ ⊔ ℓ'} B)
  --   L[A]≃L[B] = tran≃ (sym≃ A≃L[A]) (tran≃ eq A≃L[A])

  --   L[B]isSet : isSet (Lift {ℓ = ℓ ⊔ ℓ'} B)
  --   L[B]isSet = transport isSet (ua L[A]≃L[B]) L[A]isSet
    
--Ex3.5
module Ex3-5 where
  open import Base
  open import Ch3-3
  open import Ch3-6
  open import Ch3-11

  isPropA≃[A→isContrA] : ∀ {ℓ} {A : Set ℓ} → isProp A ≃ (A → isContr A)
  isPropA≃[A→isContrA] = P≃Q isPropAisProp (ΠisProp (λ x → isContrAisProp))
                             (λ p a → a , p a)
                             (λ f x y →  pr₂ (f x) x ⁻¹ ▪ pr₂ (f x) y)
  
