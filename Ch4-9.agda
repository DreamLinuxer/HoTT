{-# OPTIONS --without-K #-}
module Ch4-9 where
open import Base
open import Ch3-11
open import Ch4-2
open import Ch4-3
open import Ch4-4
open import Ch4-7
open import Ch4-8
open import Level

-- Definition 4.9.1
weak-funextentionality : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} → Set _
weak-funextentionality {A = A} {P} = ((x : A) → isContr (P x)) → isContr ((x : A) → (P x))

-- Lemma 4.9.2
≃→[ΠXA≃ΠXB] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {X : Set ℓ''}
            → A ≃ B → (X → A) ≃ (X → B)
≃→[ΠXA≃ΠXB] {ℓ} {ℓ'} {ℓ''} {A} {B} {X} (𝒇 , eq) with isequiv→qinv eq
≃→[ΠXA≃ΠXB] {ℓ} {ℓ'} {ℓ''} {A} {B} {X} (𝒇 , eq) | 𝒈 , ε , η = (_∘_ 𝒇)
                                                           , qinv→isequiv (_∘_ 𝒈 , (λ h → funext (λ x → ε (h x)))
                                                                                 , (λ h → funext (λ x → η (h x))))

-- Corollary 4.9.3
[ΣPx]≃[A] : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'}
          → ((x : A) → isContr (P x)) → isequiv {A = Σ A P} pr₁
[ΣPx]≃[A] contr = ≃→ (isContract≃isequiv pr₁) (λ x → ≃isContr (contr x) (fib[pr₁a]≃Ba x ⁻¹≃))

[A→ΣPx]≃[A→A] : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'}
              → ((x : A) → isContr (P x)) → (A → Σ A P) ≃ (A → A)
[A→ΣPx]≃[A→A] {A = A} {P} contr = ≃→[ΠXA≃ΠXB] (pr₁ , [ΣPx]≃[A] contr)

isContr[fib[id]] : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'}
                 → (contr : (x : A) → isContr (P x))
                 → isContr (fib (≃→ ([A→ΣPx]≃[A→A] contr)) id)
isContr[fib[id]] contr = hae→isContr[fib] (≃→ (biinv≃ishae _) (pr₂ ([A→ΣPx]≃[A→A] contr))) id

-- Theorem 4.9.4
isretract-fib[id]-ΠAP : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'}
                      → (contr : (x : A) → isContr (P x))
                      → is-retract (fib (≃→ ([A→ΣPx]≃[A→A] contr)) id) ((x : A) → P x)
isretract-fib[id]-ΠAP {A = A} {P} contr = ψ , φ , refl
  where
  α = (≃→ ([A→ΣPx]≃[A→A] contr))
  φ : ((x : A) → P x) → (fib α id)
  φ f = (λ x → x , f x) , refl _

  ψ : (fib α id) → ((x : A) → P x)
  ψ (g , p) = λ x → transport (λ f → P (f x)) p (pr₂ (g x))

weak-funext : ∀ {ℓ} {ℓ'} {A : Set ℓ} {P : A → Set ℓ'}
            → weak-funextentionality {ℓ} {ℓ'} {A} {P}
weak-funext contr = retract-prv-contra (isretract-fib[id]-ΠAP contr) (isContr[fib[id]] contr)

-- Theorem 4.9.5
funextentionality' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (f g : (x : A) → B x)
                   → isequiv (happly {f = f} {g = g})
funextentionality' {A = A} {B} f = isequv[total]→fibeq (isContr→isequiv contr₁ contr₂ (λ x → pr₁ x , happly (pr₂ x)))
  where
  contr₁ : isContr (Σ[ g ∈ ((x : A) → B x) ] (f ≡ g))
  contr₁ = Σ[a≡x]isContr _ f

  contr₂ : isContr (Σ[ g ∈ ((x : A) → B x) ] (f ~ g))
  contr₂ = ≃isContr (weak-funext (λ a → Σ[a≡x]isContr (B a) (f a))) (Π→ , Π→≃)
