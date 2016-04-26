{-# OPTIONS --without-K #-}
open import Level using (Lift; Level)

module Ch2-12 where
open import Ch2-11 public

--2.12
module Coproduct where
  code : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} → A + B → Set _
  code {a₀ = a₀} (inl a) = a₀ ≡ a
  code {a₀ = a₀} (inr b) = Lift 𝟘

--Theorem 2.12.5
  encode : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (p : inl a₀ ≡ x)
         → code {a₀ = a₀} x
  encode {ℓ} {ℓ'} {A} {B} {a₀} x p = transport code p (refl a₀)

  decode : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (c : code {a₀ = a₀} x)
         → inl a₀ ≡ x
  decode {a₀ = a₀} (inl a) c = ap inl c
  decode {a₀ = a₀} (inr b) c = rec𝟘 (inl a₀ ≡ inr b) (Level.lower c)

  decode∘encode~id : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (p : inl a₀ ≡ x)
                   → decode x (encode x p) ≡ p
  decode∘encode~id {A = A} {a₀ = a₀} x p =
                   ind≡' (inl a₀) (λ x₁ p₁ → decode x₁ (encode x₁ p₁) ≡ p₁)
                         (refl (refl (inl a₀))) x p

  encode∘decode~id : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (c : code {a₀ = a₀} x)
                   → encode x (decode x c) ≡ c
  encode∘decode~id {a₀ = a₀} (inl a) c =  transport code (ap inl c) (refl a₀)
                                       ≡⟨ transport[P∘f,p,u]≡transport[P,ap[f,p],u] inl code c (refl a₀) ⁻¹ ⟩
                                         transport (λ a → a₀ ≡ a) c (refl a₀)
                                       ≡⟨ transport[x↦a≡x] a₀ c (refl a₀) ⟩
                                         refl a₀ ▪ c
                                       ≡⟨ unit-left c ⁻¹ ⟩
                                         c ∎
  encode∘decode~id {a₀ = a₀} (inr b) c = rec𝟘 (encode (inr b) (decode (inr b) c) ≡ c) (Level.lower c)

  ≃+ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) → (inl a₀) ≡ x ≃ code x
  ≃+ {a₀ = a₀} x = (encode x)
                 , qinv→isequiv ((decode x) , ( encode∘decode~id x
                                            , decode∘encode~id x))

𝟚≃𝟙+𝟙 : 𝟚 ≃ 𝟙 + 𝟙
𝟚≃𝟙+𝟙 = (λ { 0₂ → inl ⊤ ; 1₂ → inr ⊤ })
      , qinv→isequiv ( rec+ 𝟚 (λ _ → 0₂) (λ _ → 1₂)
                     , ((λ {(inl ⊤) → refl (inl ⊤) ; (inr ⊤) → refl (inr ⊤)})
                     ,  (λ { 0₂ → refl 0₂ ; 1₂ → refl 1₂ })))

0₂≠1₂ : 0₂ ≠ 1₂
0₂≠1₂ eq = Level.lower (Coproduct.encode (inr ⊤) (ap (λ { 0₂ → inl ⊤ ; 1₂ → inr ⊤ }) eq))

transport[x→Ax+Bx]l : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} {x₁ x₂ : X} (p : x₁ ≡ x₂) (a : A x₁)
                    → transport (λ x → A x + B x ) p (inl a) ≡ inl (transport A p a)
transport[x→Ax+Bx]l {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x₁} {x₂} p a =
                    ind≡ (λ x₁ x₂ p → (a : A x₁)
                                    → transport (λ x → A x + B x ) p (inl a) ≡ inl (transport A p a))
                         (λ x₁ a → refl (inl a))
                         x₁ x₂ p a

transport[x→Ax+Bx]r : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} {x₁ x₂ : X} (p : x₁ ≡ x₂) (b : B x₁)
                    → transport (λ x → A x + B x ) p (inr b) ≡ inr (transport B p b)
transport[x→Ax+Bx]r {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x₁} {x₂} p b =
                    ind≡ (λ x₁ x₂ p → (b : B x₁)
                                    → transport (λ x → A x + B x ) p (inr b) ≡ inr (transport B p b))
                         (λ x₁ b → refl (inr b))
                         x₁ x₂ p b
