{-# OPTIONS --without-K #-}
module Ch5-8 where
open import Base
open import Level

U∙ : ∀ {ℓ} → Set _
U∙ {ℓ} = Σ[ A ∈ Set ℓ ] A

∙pred : ∀ {ℓ₁ ℓ₂} → U∙ {ℓ₁} → Set _
∙pred {ℓ₁} {ℓ₂} (A , a₀) = Σ[ R ∈ (A → Set ℓ₂) ] R a₀

ppmap : ∀ {ℓ₁ ℓ₂ ℓ₃} {A∙ : U∙ {ℓ₁}} → (R : ∙pred {ℓ₂ = ℓ₂} A∙) (S : ∙pred {ℓ₂ = ℓ₃} A∙) → Set (ℓ₃ ⊔ ℓ₂ ⊔ ℓ₁)
ppmap {A∙ = A , a₀} (R , r₀) (S , s₀) = Σ[ g ∈ ((b : A) → R b → S b) ] g a₀ r₀ ≡ s₀

isIdsys : ∀ {ℓ₁ ℓ₂ ℓ₃} {A∙ : U∙ {ℓ₁}} (R : ∙pred {ℓ₂ = ℓ₂} A∙) → Set (suc ℓ₃ ⊔ (ℓ₂ ⊔ ℓ₁))
isIdsys {ℓ₁} {ℓ₂} {ℓ₃} {A∙ = A , a₀} (R , r₀) = (D : (b : A) → R b → Set ℓ₃) (d : D a₀ r₀)
                                             → Σ[ f ∈ ((b : A) (r : R b)→ D b r) ] f a₀ r₀ ≡ d
