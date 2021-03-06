{-# OPTIONS --without-K #-}

module Ch2-1 where
open import Ch1 public

infixr 20 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (g : B → C) → (f : A → B) → (A → C)
_∘_ g f = (λ x → g (f x))

--2.1
--Lemma 2.1.1
infix 20 _⁻¹
_⁻¹ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
_⁻¹ {ℓ} {A} {x} {y} = ind≡ (λ x y x≡y → y ≡ x) (λ x → refl x) x y

--Lemma 2.1.2
infixl 10 _▪_
_▪_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_▪_ {ℓ} {A} {x} {y} {z} x≡y y≡z = ind≡ (λ x y x≡y → (z : A) → (y≡z : y ≡ z) → x ≡ z)
                                       (ind≡ (λ x z x≡z → x ≡ z) (λ x → refl x))
                                       x y x≡y z y≡z

--Lemma 2.1.4
unit-right : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ≡ p ▪ (refl y)
unit-right {ℓ} {A} {x} {y} = ind≡ (λ x y p → p ≡ p ▪ refl y) (λ x → refl (refl x)) x y

unit-left : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ≡ (refl x) ▪ p
unit-left {ℓ} {A} {x} {y} = ind≡ (λ x y p → p ≡ (refl x) ▪ p)
                             (λ x → refl (refl x)) x y

p⁻¹▪p≡refly : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⁻¹ ▪ p ≡ refl y
p⁻¹▪p≡refly {ℓ} {A} {x} {y} = ind≡ (λ x y p → p ⁻¹ ▪ p ≡ refl y)
                                   (λ x → refl (refl x)) x y

p▪p⁻¹≡reflx : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ▪ p ⁻¹ ≡ refl x
p▪p⁻¹≡reflx {ℓ} {A} {x} {y} = ind≡ (λ x y p → p ▪ p ⁻¹ ≡ refl x)
                                   (λ x → refl (refl x)) x y

p⁻¹⁻¹≡p : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
p⁻¹⁻¹≡p {ℓ} {A} {x} {y} = ind≡ (λ x y p → p ⁻¹ ⁻¹ ≡ p)
                               (λ x → refl (refl x)) x y

assoc▪ : ∀ {ℓ} {A : Set ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ▪ (q ▪ r) ≡ (p ▪ q) ▪ r
assoc▪ {ℓ} {A} {x} {y} {z} {w} p q r =
  ind≡ (λ x y p → (z w : A) → (q : y ≡ z) → (r : z ≡ w) → p ▪ (q ▪ r) ≡ (p ▪ q) ▪ r)
       (λ x z w q r →
         ind≡ (λ x z q → (w : A) → (r : z ≡ w) → refl x ▪ (q ▪ r) ≡ (refl x ▪ q) ▪ r)
              (λ x w r →
                ind≡ (λ x w r → refl x ▪ (refl x ▪ r) ≡ (refl x ▪ refl x) ▪ r)
                     (λ x → refl (refl x))
                     x w r)
              x z q w r)
       x y p z w q r

1-path : {A : Set} {x y : A} → Set
1-path {A} {x} {y} = x ≡ y

2-path : {A : Set} {x y : A} → {p q : x ≡ y} → Set
2-path {A} {x} {y} {p} {q}= p ≡ q

3-path : {A : Set} {x y : A} → {p q : x ≡ y} → {α β : p ≡ q} → Set
3-path {A} {x} {y} {p} {q} {α} {β} = α ≡ β

Ω : {A : Set} {a : A}  → Set
Ω {A} {a} = 1-path {A} {a} {a}

Ω² : {A : Set} {a : A} → Set
Ω² {A} {a} = 2-path {A} {a} {a} {refl a} {refl a}

infixr 1 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ α ⟩ β = α ▪ β

infix 2 _∎
_∎ : ∀ {ℓ} {A : Set ℓ} (p : A) → p ≡ p
p ∎ = refl p

--Theorem 2.1.6
_▪r_ : {A : Set} {a b c : A}
       {p q : 1-path {A} {a} {b}}
       (α : 2-path {A} {a} {b} {p} {q})
       (r : 1-path {A} {b} {c}) →
       p ▪ r ≡ q ▪ r
_▪r_ {A} {a} {b} {c} {p} {q} α r =
  ind≡ (λ b c r → (p q : a ≡ b) → (α : p ≡ q) → p ▪ r ≡ q ▪ r)
       (λ b p q α → unit-right p ⁻¹ ▪ α ▪ unit-right q)
       b c r p q α

_▪l_ : {A : Set} {a b c : A}
       {r s : 1-path {A} {b} {c}}
       (q : 1-path {A} {a} {b})
       (β : 2-path {A} {b} {c} {r} {s}) →
       q ▪ r ≡ q ▪ s
_▪l_ {A} {a} {b} {c} {r} {s} q β =
  ind≡ (λ a b q → (r s : b ≡ c) → (β : r ≡ s) → q ▪ r ≡ q ▪ s)
       (λ b r s β → (unit-left r) ⁻¹ ▪ β ▪ unit-left s)
       a b q r s β

_★_ : {A : Set} {a b c : A}
      {p q : 1-path {A} {a} {b}}
      {r s : 1-path {A} {b} {c}}
      (α : 2-path {A} {a} {b} {p} {q})
      (β : 2-path {A} {b} {c} {r} {s}) →
      p ▪ r ≡ q ▪ s
_★_ {A} {a} {b} {c} {p} {q} {r} {s} α β = (α ▪r r) ▪ (q ▪l β)

_★'_ : {A : Set} {a b c : A}
       {p q : 1-path {A} {a} {b}}
       {r s : 1-path {A} {b} {c}}
       (α : 2-path {A} {a} {b} {p} {q})
       (β : 2-path {A} {b} {c} {r} {s}) →
       p ▪ r ≡ q ▪ s
_★'_ {A} {a} {b} {c} {p} {q} {r} {s} α β = (p ▪l β) ▪ (α ▪r s)

refl▪lβ≡β : {A : Set} {a : A}
            (β : Ω²) →
            refl a ▪l β ≡ β
refl▪lβ≡β {A} {a} β =
             refl a ▪l β
          ≡⟨ refl _ ⟩
             refl (refl a) ▪ β ▪ refl (refl a)
          ≡⟨ (unit-right (refl (refl a) ▪ β)) ⁻¹ ⟩
             refl (refl a) ▪ β
          ≡⟨ unit-left β ⁻¹ ⟩
             (β ∎)

α▪rrefl≡α : {A : Set} {a : A}
            (α : Ω²) →
            α ▪r refl a ≡ α
α▪rrefl≡α {A} {a} α =
              α ▪r refl a
           ≡⟨ refl _ ⟩
              refl (refl a) ▪ α ▪ refl (refl a)
           ≡⟨ (unit-right (refl (refl a) ▪ α)) ⁻¹ ⟩
              refl (refl a) ▪ α
           ≡⟨ (unit-left α) ⁻¹ ⟩
              (α ∎)

α★β≡α▪β : {A : Set} {a : A}
          {α β : Ω² {A} {a}} →
          α ★ β ≡ α ▪ β
α★β≡α▪β {A} {a} {α} {β} =
            α ★ β
        ≡⟨ refl _ ⟩
           (α ▪r refl a) ▪ (refl a ▪l β)
        ≡⟨ ind≡ (λ p q γ → p ▪ (refl a ▪l β) ≡ q ▪ (refl a ▪l β))
                (λ p → refl _) (α ▪r refl a) α (α▪rrefl≡α α) ⟩
           α ▪ (refl a ▪l β)
        ≡⟨ ind≡ (λ p q γ → α ▪ p ≡ α ▪ q)
                (λ p → refl _) (refl a ▪l β) β (refl▪lβ≡β β) ⟩
           α ▪ β ∎

α★'β≡β▪α : {A : Set} {a : A}
           {α β : Ω² {A} {a}} →
           α ★' β ≡ β ▪ α
α★'β≡β▪α {A} {a} {α} {β} =
             α ★' β
          ≡⟨ refl _ ⟩
             refl a ▪l β ▪ α ▪r refl a
          ≡⟨ ind≡ (λ p q γ → p ▪ α ▪r refl a ≡ q ▪ α ▪r refl a)
                  (λ p → refl _) (refl a ▪l β) β (refl▪lβ≡β β) ⟩
             β ▪ α ▪r refl a
          ≡⟨ ind≡ (λ p q γ → β ▪ p ≡ β ▪ q)
                  (λ p → refl _) (α ▪r refl a) α (α▪rrefl≡α α) ⟩
             β ▪ α ∎

α★β≡α★'β' : {A : Set} {a b c : A}
            (p : a ≡ b) → (r : b ≡ c) →
            refl p ★ refl r ≡ refl p ★' refl r
α★β≡α★'β' {A} {a} {b} {c} p r =
          ind≡ (λ a b p → (c : A) → (r : b ≡ c) → refl p ★ refl r ≡ refl p ★' refl r)
               (λ a c r →
                  ind≡ (λ a c r → refl (refl a) ★ refl r ≡ refl (refl a) ★' refl r)
                       (λ a → refl (refl (refl a)))
                       a c r)
               a b p c r

α★β≡α★'β : {A : Set} {a : A}
           {α β : Ω² {A} {a}} →
           α ★ β ≡ α ★' β
α★β≡α★'β {A} {a} {α} {β} =
         ind≡ (λ p q α → (β : Ω² {A} {a}) → α ★ β ≡ α ★' β)
              (λ p β → ind≡ (λ r s β → refl p ★ β ≡ refl p ★' β)
                            (λ r → α★β≡α★'β' p r)
                            (refl a) (refl a) β)
              (refl a) (refl a) α β

Eckerman-Hilton : {A : Set} {a : A} →
                  (α β : Ω² {A} {a}) →
                  α ▪ β ≡ β ▪ α
Eckerman-Hilton {A} {a} α β =
                    α ▪ β
                 ≡⟨ α★β≡α▪β {α = α} {β = β} ⁻¹ ⟩
                    α ★ β
                 ≡⟨ α★β≡α★'β {α = α} {β = β} ⟩
                    α ★' β
                 ≡⟨ α★'β≡β▪α {α = α} {β = β} ⟩
                    β ▪ α ∎
