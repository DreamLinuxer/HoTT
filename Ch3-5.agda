{-# OPTIONS --without-K #-}
module Ch3-5 where
open import Base
open import Ch3-1
open import Ch3-3
import Level as L

--Lemma 3.5.1
subset≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} → ((x : A) → isProp (P x))
        → (u v : Σ[ x ∈ A ] P x) → pr₁ u ≡ pr₁ v → u ≡ v
subset≡ {P = P} f u v p with Σ≃ {w = u} {w' = v}
subset≡ {P = P} f u v p | 𝒇 , (g , α) , (h , β) = h (p , f (pr₁ v) (transport P p (pr₂ u)) (pr₂ v))

SetU : ∀ {ℓ} → Set _
SetU {ℓ} = Σ[ A ∈ Set ℓ ] isSet A

PropU : ∀ {ℓ} → Set _
PropU {ℓ} = Σ[ A ∈ Set ℓ ] isProp A

postulate
  SetRes : ∀ {ℓ} → SetU {ℓ} → SetU {L.suc ℓ}
  PropRes : ∀ {ℓ} → PropU {ℓ} → PropU {L.suc ℓ}
--axiom 3.5.5
  PropResizing : ∀ {ℓ} → isequiv (PropRes {ℓ})
