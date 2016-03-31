{-# OPTIONS --without-K #-}

module Ch2-12 {ℓ} {ℓ'} where
open import Level using (Lift)
open import Ch2-11 public

--2.12

code : {A : Set ℓ} {B : Set ℓ'} {a₀ : A} → A + B → Set ℓ
code {a₀ = a₀} (inl a) = a₀ ≡ a
code {a₀ = a₀} (inr b) = Lift 𝟘

encode : {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (p : inl a₀ ≡ x)
       → code {a₀ = a₀} x
encode {A} {B} {a₀} x p = transport code p (refl a₀)

decode : {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (c : code {a₀ = a₀} x)
       → inl a₀ ≡ x
decode {a₀ = a₀} (inl a) c = ap inl c
decode {a₀ = a₀} (inr b) c = rec𝟘 (inl a₀ ≡ inr b) (Level.lower c)

decode∘encode~id : {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (p : inl a₀ ≡ x)
                 → decode x (encode x p) ≡ p
decode∘encode~id {A = A} {a₀ = a₀} x p =
                 ind≡' (inl a₀) (λ x₁ p₁ → decode x₁ (encode x₁ p₁) ≡ p₁)
                       (refl (refl (inl a₀))) x p

encode∘decode~id : {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (c : code {a₀ = a₀} x)
                 → encode x (decode x c) ≡ c
encode∘decode~id (inl a) c = {!!}
encode∘decode~id (inr b) c = rec𝟘 (encode (inr b) (decode (inr b) c) ≡ c) (Level.lower c)
