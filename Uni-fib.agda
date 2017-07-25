{-# OPTIONS --without-K #-}

module Uni-fib where
open import Base
open import Ch3-3
open import Ch3-7

IsUnivFib : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂)  → Set _
IsUnivFib {A = A} B = {a a' : A} → isequiv {A = (a ≡ a')} {B = (B a ≃ B a')} (idtoeqv ∘ ap B)

Ω : ∀ {ℓ} {X : Set ℓ} (x : X) → Set _
Ω x = x ≡ x

BAut : ∀ {ℓ} (F : Set ℓ) → Set _
BAut F = Σ[ Y ∈ (Set _) ] (∥ Y ≡ F ∥)

Aut : ∀ {ℓ} (F : Set ℓ) → Set _
Aut F = F ≃ F

BAut≃ :  ∀ {ℓ} {X : Set ℓ} (X₁ X₂ : BAut X) → (X₁ ≡ X₂) ≃ (pr₁ X₁ ≃ pr₁ X₂)
BAut≃ {X = X} (A , p) (B , q) = f , qinv→isequiv (g , α , β)
  where
  f : (A , p) ≡ (B , q) → A ≃ B
  f = idtoeqv ∘ ap pr₁

  g : A ≃ B → (A , p) ≡ (B , q)
  g eq = pairΣ≡ (ua eq , inhabPath _ _)

  α : f ∘ g ~ id
  α eq = ap idtoeqv (pairΣ≡₁ (ua eq , inhabPath _ _)) ▪ comp≡ eq ⁻¹

  β : g ∘ f ~ id
  β (refl _) = ap pairΣ≡ (pairΣ≡ ((uniq≡ _)⁻¹ , (PropisSet inhabPath _ _ _ _)))

ΩBAut≃Aut : ∀ {ℓ} {X : Set ℓ} → Ω (X , ∣ refl _ ∣) ≃ Aut X
ΩBAut≃Aut {X = X} = BAut≃ (X , ∣ refl _ ∣) (X , ∣ refl _ ∣)
