{-# OPTIONS --without-K #-}
module Ch4-8 where
open import Base
open import Ch3-11
open import Ch4-2
open import Ex2
open import Level

-- Lemma 4.8.1
fib[pr₁a]≃Ba : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (a : A)
             → fib (pr₁ {B = B}) a ≃ B a
fib[pr₁a]≃Ba {A = A} {B} a = fib pr₁ a
                          ≃⟨ sym≃ Ex2-10.assocΣ ⟩
                             Σ[ x ∈ A ] Σ[ b ∈ B x ] x ≡ a
                          ≃⟨ ≃→Σ≃ (λ x → swap×≃) ⟩
                             Σ[ x ∈ A ] Σ[ p ∈ x ≡ a ] B x
                          ≃⟨ Ex2-10.assocΣ ⟩
                             Σ[ w ∈ Σ[ x ∈ A ] (x ≡ a) ] B (pr₁ w)
                          ≃⟨ isContrA→ΣPx≃Pa _ _ (Σ[x≡a]isContr A a) ⟩
                             B a ∎≃

-- Lemma 4.8.2
-- A≃Σ[fib] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
--          → A ≃ (Σ[ b ∈ B ] fib f b)
-- A≃Σ[fib] {A = A} {B} {f} = A
--                         ≃⟨ (isContrP→ΣPx≃A _ _ (λ a → Σ[a≡x]isContr B (f a))) ⁻¹≃ ⟩
--                            Σ[ a ∈ A ] Σ[ b ∈ B ] f a ≡ b
--                         ≃⟨ (λ {(a , b , p) → (b , a , p)})
--                           , (qinv→isequiv ( (λ {(b , a , p) → (a , b , p)})
--                                           , (λ {(b , a , p) → refl _})
--                                           , (λ {(a , b , p) → refl _}))) ⟩
--                            (Σ[ b ∈ B ] fib f b) ∎≃

A≃Σ[fib] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
         → A ≃ (Σ[ b ∈ B ] fib f b)
A≃Σ[fib] {A = A} {B} {f} = (λ a → f a , a , refl _)
                         , (qinv→isequiv ( (λ {(b , a , p) → a})
                                         , (λ {(b , a , p) → ap (λ {(b , a , p) → a , b , p})
                                                                (pairΣ≡ ((refl a) , pr₂ (Σ[a≡x]isContr B (f a)) _))})
                                         , (λ a → refl _)))

-- Theorem 4.8.3
Σ[A→B]≃[B→U] : ∀ {ℓ ℓ'} {B : Set ℓ'} → (Σ[ A ∈ Set (ℓ ⊔ ℓ') ] (A → B)) ≃ (B → Set (ℓ ⊔ ℓ'))
Σ[A→B]≃[B→U] {ℓ} {ℓ'} {B} = 𝓧 , qinv→isequiv (ψ , η , ε)
  where
  𝓧 : (Σ[ A ∈ Set (ℓ ⊔ ℓ') ] (A → B)) → B → Set (ℓ ⊔ ℓ')
  𝓧 (A , f) b = fib f b

  ψ : (B → Set (ℓ ⊔ ℓ')) → (Σ[ A ∈ Set (ℓ ⊔ ℓ') ] (A → B))
  ψ P = (Σ[ b ∈ B ] (P b)) , pr₁

  η : 𝓧 ∘ ψ ~ id
  η P = funext (λ b → ua (fib[pr₁a]≃Ba {A = B} {B = P} b))

  ε : ψ ∘ 𝓧 ~ id
  ε (A , f) = pairΣ≡ (ua A≃Σ[fib] ⁻¹ , funext r)
    where
    r : (a : A) → transport (λ A → A → B) (ua (A≃Σ[fib] {f = f}) ⁻¹) pr₁ a  ≡ f a
    r a = transport (λ A → A → B) (ua (A≃Σ[fib] {f = f}) ⁻¹) pr₁ a
       ≡⟨ ap (λ f → f a) (transport→ {A = id} {B = λ _ → B} (ua A≃Σ[fib] ⁻¹) pr₁) ⟩
          transport (λ _ → B) (ua A≃Σ[fib] ⁻¹) (pr₁ (transport id ((ua A≃Σ[fib] ⁻¹) ⁻¹) a))
       ≡⟨ transportconst B (ua A≃Σ[fib] ⁻¹) _ ⟩
          (pr₁ (transport id ((ua A≃Σ[fib] ⁻¹) ⁻¹) a))
       ≡⟨ ap (λ x → pr₁ (transport id x a)) (p⁻¹⁻¹≡p (ua A≃Σ[fib])) ⟩
          (pr₁ (transport id (ua A≃Σ[fib]) a))
       ≡⟨ ap pr₁ (computation≡ A≃Σ[fib] a) ⟩
          f a ∎

-- Theorem 4.8.4
𝒪 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → A → Σ[ A ∈ Set _ ] A
𝒪 f = λ a → (fib f (f a) , (a , refl (f a)))

  module Theorem-4-8-4 where
  open Ex2-11
  open Ex2-10
  A≃B×[U]U● : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
            → A ≃ (B ×[ (Set _) ] (Σ[ A ∈ Set _ ] A)) (fib f) pr₁
  A≃B×[U]U● {A = A} {B} f = A
                         ≃⟨ A≃Σ[fib] ⟩
                            Σ[ b ∈ B ] fib f b
                         ≃⟨ ≃→Σ≃ eq ⟩
                            Σ[ b ∈ B ] Σ[ X ∈ (Set _) ] Σ[ p ∈ (fib f b ≡ X) ] X
                         ≃⟨ ≃→Σ≃ (λ b → ≃→Σ≃ (λ X → swap×≃)) ⟩
                            Σ[ b ∈ B ] Σ[ X ∈ (Set _) ] Σ[ x ∈ X ] (fib f b ≡ X)
                         ≃⟨ ≃→Σ≃ (λ b → assocΣ) ⟩
                            (Σ[ b ∈ B ] Σ[ Y ∈ Σ[ X ∈ (Set _) ] X ] (fib f b ≡ pr₁ Y)) ∎≃
            where
            eq : (b : B) → fib f b ≃ (Σ[ X ∈ (Set _) ] Σ[ p ∈ (fib f b ≡ X) ] X)
            eq b = f' , qinv→isequiv (g' , ε , refl)
               where
               f' = λ fi → (fib f b) , refl _ , fi
               g' : (Σ[ X ∈ (Set _) ] Σ[ p ∈ (fib f b ≡ X) ] X) → fib f b
               g' (_ , refl _ , x) = x

               ε : f' ∘ g' ~ id
               ε (_ , refl _ , x) = refl _

