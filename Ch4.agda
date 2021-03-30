{-# OPTIONS --without-K #-}
module Ch4 where
open import Base
open import Ch4-1 public
open import Ch4-2 public
open import Ch4-3 public
open import Ch4-4 public
open import Ch4-6 public
open import Ch4-7 public
open import Ch4-8 public
open import Ch4-9 public

≃→≃Σ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {P : A → Set ℓ₃} {Q : B → Set ℓ₄}
     → (eq : A ≃ B) → ((a : A) → P a ≃ Q ((≃→ eq) a))
     → Σ A P ≃ Σ B Q
≃→≃Σ {A = A} {B} {P} {Q} (𝒇 , eq₁) eq₂ with (≃→ (biinv≃ishae 𝒇)) eq₁
... | (𝒈 , ε , η , τ) = f , qinv→isequiv ( g , ε' , η' )
     where
     f : Σ A P → Σ B Q
     f (a , p) = 𝒇 a , (≃→ (eq₂ a)) p

     g : Σ B Q → Σ A P
     g (b , q) = 𝒈 b , (≃← (eq₂ (𝒈 b)) (transport Q (ε b ⁻¹) q))

     ε' : f ∘ g ~ id
     ε' (b , q) = pairΣ≡ ( (ε b)
                        , ((ε b *) (≃→ (eq₂ (𝒈 b)) (≃← (eq₂ (𝒈 b)) (transport Q (ε b ⁻¹) q)))
                        ≡⟨ ap (ε b *) (≃ε (eq₂ (𝒈 b)) _) ⟩
                           (ε b *) (transport Q (ε b ⁻¹) q)
                        ≡⟨ transport▪ Q (ε b ⁻¹) (ε b) q ⟩
                           ((ε b ⁻¹ ▪ ε b) *) q
                        ≡⟨ ap (λ p → (_* {P = Q} p) q) (p⁻¹▪p≡refly (ε b)) ⟩
                           q ∎))

     η' : g ∘ f ~ id
     η' (a , p) = pairΣ≡ ( (η a)
                         , ((η a *) (≃← (eq₂ (𝒈 (𝒇 a))) (transport Q (ε (𝒇 a) ⁻¹) (≃→ (eq₂ a) p)))
                         ≡⟨ transport∘f (λ a → Q (𝒇 a)) P
                            (λ a → (≃← (eq₂ a))) (η a) (transport Q (ε (𝒇 a) ⁻¹) (≃→ (eq₂ a) p)) ⟩
                            ≃← (eq₂ a) (transport (λ a → Q (𝒇 a)) (η a) (transport Q (ε (𝒇 a) ⁻¹) (≃→ (eq₂ a) p)))
                         ≡⟨ ap (≃← (eq₂ a)) (transport[P∘f] 𝒇 Q (η a) (transport Q (ε (𝒇 a) ⁻¹) (≃→ (eq₂ a) p))) ⟩
                            ≃← (eq₂ a) (transport Q (ap 𝒇 (η a)) (transport Q (ε (𝒇 a) ⁻¹) (≃→ (eq₂ a) p)))
                         ≡⟨ ap (λ x → ≃← (eq₂ a) (transport Q x (transport Q (ε (𝒇 a) ⁻¹) (≃→ (eq₂ a) p)))) (τ a) ⟩
                            ≃← (eq₂ a) (transport Q (ε (𝒇 a)) (transport Q (ε (𝒇 a) ⁻¹) (≃→ (eq₂ a) p)))
                         ≡⟨ ap (≃← (eq₂ a)) (transport▪ Q (ε (𝒇 a) ⁻¹) (ε (𝒇 a)) _) ⟩
                            ≃← (eq₂ a) (transport Q (ε (𝒇 a) ⁻¹ ▪ ε (𝒇 a)) (≃→ (eq₂ a) p))
                         ≡⟨ ap (λ x → ≃← (eq₂ a) (transport Q x (≃→ (eq₂ a) p))) (p⁻¹▪p≡refly (ε (𝒇 a))) ⟩
                            ≃← (eq₂ a) (≃→ (eq₂ a) p)
                         ≡⟨ ≃η (eq₂ a) p ⟩
                            p ∎))
