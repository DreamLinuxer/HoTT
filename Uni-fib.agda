{-# OPTIONS --without-K #-}

module Uni-fib where

import Level as L using (_⊔_; suc)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

_~_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f g : A → B) → Set _
_~_ {A = A} f g = (a : A) → f a ≡ g a

IsEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set _
IsEquiv {A = A} {B = B} f = (Σ[ g ∈ (B → A) ] ((f ∘ g) ~ id) ) × (Σ[ h ∈ (B → A) ] ((h ∘ f) ~ id) )

_≃_ : ∀ {ℓ} (A B : Set ℓ) → Set _
A ≃ B = Σ[ f ∈ (A → B) ] IsEquiv f

ω : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
ω refl = id , (id , (λ _ → refl)) , (id , (λ _ → refl))

ap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) → {a a' : A} → a ≡ a' → (B a ≡ B a')
ap B refl = refl

IsUnivFib : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂)  → Set _
IsUnivFib {A = A} B = {a a' : A} → IsEquiv {A = (a ≡ a')} {B = (B a ≃ B a')} (ω ∘ ap B)

isProp : ∀ {ℓ} (P : Set ℓ) → Set _
isProp P = (x y : P) → x ≡ y

data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
  ∣_∣ : A → ∥ A ∥
postulate
  truncationIsProp : ∀ {ℓ} {A : Set ℓ} → isProp ∥ A ∥

⟦_⟧ : ∀ {ℓ} (F : Set ℓ) → Set _
⟦_⟧ F = Σ[ Y ∈ (Set _) ] (∥ Y ≡ F ∥)

UA : ∀ {ℓ} {A : Set ℓ} → Set _
UA {ℓ} {A} = IsUnivFib {ℓ₁ = L.suc ℓ} id

module ex1 where
  𝟙 : Set
  𝟙 = ⊤

  P : 𝟙 → Set
  P = λ _ → 𝟙

  PIsUnivFib : IsUnivFib P
  PIsUnivFib = ((λ _ → refl) , (λ {a → {!!}}))
             , ((λ x → refl) , (λ {refl → refl}))

module ex2 where
  𝟙 𝟘 : Set
  𝟙 = ⊤
  𝟘 = ⊥

  P : 𝟙 → Set
  P = λ _ → 𝟘

  PIsUnivFib : IsUnivFib P
  PIsUnivFib = ((λ _ → refl) , (λ {a → {!!}}))
             , ((λ x → refl) , (λ {refl → refl}))
