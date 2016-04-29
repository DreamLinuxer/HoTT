{-# OPTIONS --without-K #-}

module Ch2-15 where
open import Ch2-14 public

--2.15.1
×→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : Set ℓ'} {B : Set ℓ''}
   → (X → A × B) → (X → A) × (X → B)
×→ f = (pr₁ ∘ f) , (pr₂ ∘ f)

--Theorem 2.15.2
×→≃ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : Set ℓ'} {B : Set ℓ''}
    → isequiv (×→ {X = X} {A = A} {B = B})
×→≃ = qinv→isequiv ( (λ {(g , h) → λ x → (g x , h x)})
                   , ( (λ {(g , h) →  (λ x → g x) , (λ x → h x)
                                   ≡⟨ pair×≡ (refl g , refl h) ⟩
                                      (g , h) ∎})
                     , (λ f →  (λ x → ((pr₁ ∘ f) x , (pr₂ ∘ f) x))
                            ≡⟨ funext (λ x → pair×≡ ((refl (pr₁ (f x))) , (refl (pr₂ (f x))))) ⟩
                               f ∎)))
