{-# OPTIONS --without-K #-}
module Ch5-3 where
open import Base
open import Level

data W {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  sup : (a : A) → (f : B a → W A B) → W A B

ℕᵂ = W 𝟚 (rec𝟚 (Set _) 𝟘 𝟙)

List : ∀ {ℓ} (A : Set ℓ) → Set _
List A = W (𝟙 + A) (rec+ (Set _) (λ _ → 𝟘) (λ a → 𝟙))

0ᵂ 1ᵂ : ℕᵂ
0ᵂ = sup 0₂ (λ x → rec𝟘 ℕᵂ x)
1ᵂ = sup 1₂ (λ _ → 0ᵂ)

succᵂ : ℕᵂ → ℕᵂ
succᵂ = λ n → sup 1₂ (λ _ → n)

indW : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'}
     → (E : W A B → Set ℓ'')
     → (e : (a : A) (f : B a → W A B) (g : (b : B a) → E (f b)) → E (sup a f))
     → (w : W A B) → E w
indW E e (sup a f) = e a f (λ b → indW E e (f b))

doubleᵂ : ℕᵂ → ℕᵂ
doubleᵂ = indW (λ _ → ℕᵂ) (λ a → ind𝟚 (λ a → (f g : (B a) → ℕᵂ) → ℕᵂ)
                                      (λ f g → 0ᵂ)
                                      (λ f g → succᵂ (succᵂ (g ⋆))) a)
  where
  B = rec𝟚 (Set _) 𝟘 𝟙

doubleᵂ[0ᵂ] : doubleᵂ 0ᵂ ≡ 0ᵂ
doubleᵂ[0ᵂ] = refl _

doubleᵂ[1ᵂ] : doubleᵂ 1ᵂ ≡ succᵂ (succᵂ 0ᵂ)
doubleᵂ[1ᵂ] = refl _

-- Theorem 5.3.1
uniq[ΠWE] : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {E : W A B → Set ℓ₃}
          → (g h : (w : W A B) → E w)
          → (e : (a : A) (f : (B a) → W A B) → ((b : B a) → E (f b)) → E (sup a f))
          → ((a : A) (f : (B a) → W A B) → g (sup a f) ≡ e a f (λ b → g (f b)))
          → ((a : A) (f : (B a) → W A B) → h (sup a f) ≡ e a f (λ b → h (f b)))
          → g ≡ h
uniq[ΠWE] g h e g≡ h≡ = funext (λ {w → indW (λ w₁ → g w₁ ≡ h w₁)
                                            (λ a f IH → g≡ a f ▪ ap (e a f) (funext IH) ▪ h≡ a f ⁻¹) w})
