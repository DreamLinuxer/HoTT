{-# OPTIONS --without-K #-}
module Ch3-6 where
open import Base
open import Ch3-3

-- Example 3.6.1
×isProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → isProp A → isProp B → isProp (A × B)
×isProp {ℓ} {ℓ'} {A} {B} AisProp BisProp x y with ×≃ {A = A} {B = B} {x = x} {y = y}
×isProp {ℓ} {ℓ'} {A} {B} AisProp BisProp x y | (g , α) , (h , β) = g (x₁≡y₁ , x₂≡y₂)
        where
        x₁≡y₁ = AisProp (pr₁ x) (pr₁ y)
        x₂≡y₂ = BisProp (pr₂ x) (pr₂ y)

-- Example 3.6.2
ΠisProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → ((x : A) → isProp (B x))
        → isProp ((x : A) → B x)
ΠisProp A→BxisProp f g = funext (λ x → A→BxisProp x (f x) (g x))

→isProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → isProp A →  isProp B → isProp (A → B)
→isProp AisProp BisProp f g = ΠisProp (λ _ → BisProp) f g

𝟘isProp : isProp 𝟘
𝟘isProp ()

¬isProp : ∀ {ℓ} {A : Set ℓ} → isProp A → isProp (¬ A)
¬isProp AisProp = →isProp AisProp 𝟘isProp
