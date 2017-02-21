{-# OPTIONS --without-K #-}
module Ch3-3 where
open import Base
open import Ch3-1

-- Definitino 3.3.1
isProp : ∀ {ℓ} (P : Set ℓ) → Set _
isProp P = (x y : P) → x ≡ y

-- Lemma 3.3.3
P≃Q : ∀ {ℓ ℓ'} {P : Set ℓ} {Q : Set ℓ'}
    → isProp P → isProp Q → (P → Q) → (Q → P)
    → P ≃ Q
P≃Q PisProp QisProp f g = f , (qinv→isequiv (g , (α , β)))
    where
    α : f ∘ g ~ id
    α x = QisProp (f (g x)) x

    β : g ∘ f ~ id
    β x = PisProp (g (f x)) x

-- Lemma 3.3.2
P≃𝟙 : ∀ {ℓ} {P : Set ℓ} → isProp P → (x₀ : P) → P ≃ 𝟙
P≃𝟙 {ℓ} {P} PisProp x₀ =
    P≃Q PisProp (λ x y → uniq𝟙 x ▪ uniq𝟙 y ⁻¹) f g
    where
    f : P → 𝟙
    f _ = ⋆

    g : 𝟙 → P
    g ⋆ = x₀

--Lemma 3.3.4
PropisSet : ∀ {ℓ} {A : Set ℓ} → isProp A → isSet A
PropisSet {ℓ} {A} f x y p q = eq p ▪ eq q ⁻¹
          where
          g : (z : A) → x ≡ z
          g z = f x z

          eq : {y z : A} (r : y ≡ z) → r  ≡ g y ⁻¹ ▪ g z
          eq {y} {z} r = r
                      ≡⟨ unit-left r ⟩
                         refl y ▪ r
                      ≡⟨ ap (λ s → s ▪ r) (p⁻¹▪p≡refly (g y) ⁻¹) ⟩
                         g y ⁻¹ ▪ g y ▪ r
                      ≡⟨ assoc▪ (g y ⁻¹) (g y) r ⁻¹ ⟩
                         g y ⁻¹ ▪ (g y ▪ r)
                      ≡⟨ ap (λ s → g y ⁻¹ ▪ s) (transport[x↦a≡x] x r (g y) ⁻¹) ⟩
                         g y ⁻¹ ▪ (r *) (g y)
                      ≡⟨ ap (λ s → g y ⁻¹ ▪ s) (apd g r) ⟩
                         g y ⁻¹ ▪ g z ∎

--Lemma 3.3.5
isPropAisProp : ∀ {ℓ} {A : Set ℓ} → isProp (isProp A)
isPropAisProp f g = funext (λ x → funext (λ y → PropisSet f x y (f x y) (g x y)))

isSetAisProp : ∀ {ℓ} {A : Set ℓ} → isProp (isSet A)
isSetAisProp f g = funext (λ x → funext
                          (λ y → funext
                          (λ p → funext
                          (λ q → isSet→1-type f (f x y p q) (g x y p q)))))
