module Ch2 where

data _≡_ {A : Set} : (x y : A) → Set where
  refl : (x : A) → x ≡ x

infix 4 _≡_

ind≡ : {A : Set} (C : (x y : A) (p : x ≡ y) → Set) →
       ((x : A) → C x x (refl x)) →
       ((x y : A) (p : x ≡ y) → C x y p)
ind≡ C c x .x (refl .x) = c x

_∘_ : {A B C : Set} (g : B → C) → (f : A → B) → (A → C)
_∘_ g f = (λ x → g (f x))

id : {A : Set} → A → A
id a = a

--2.1
--Lemma 2.1.1
infix 20 _⁻¹
_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
_⁻¹ {A} {x} {y} = ind≡ (λ x y x≡y → y ≡ x) (λ x → refl x) x y

--Lemma 2.1.2
infixl 10 _▪_
_▪_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_▪_ {A} {x} {y} {z} x≡y y≡z = ind≡ (λ x y x≡y → (z : A) → (y≡z : y ≡ z) → x ≡ z)
                                   (ind≡ (λ x z x≡z → x ≡ z) (λ x → refl x))
                                   x y x≡y z y≡z

--Lemma 2.1.4
unit-right : {A : Set} {x y : A} (p : x ≡ y) → p ≡ p ▪ (refl y)
unit-right {A} {x} {y} = ind≡ (λ x y p → p ≡ p ▪ refl y) (λ x → refl (refl x)) x y

unit-left : {A : Set} {x y : A} (p : x ≡ y) → p ≡ (refl x) ▪ p
unit-left {A} {x} {y} = ind≡ (λ x y p → p ≡ (refl x) ▪ p)
                             (λ x → refl (refl x)) x y

p⁻¹▪p≡refly : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ▪ p ≡ refl y
p⁻¹▪p≡refly {A} {x} {y} = ind≡ (λ x y p → p ⁻¹ ▪ p ≡ refl y)
                               (λ x → refl (refl x)) x y

p▪p⁻¹≡reflx : {A : Set} {x y : A} (p : x ≡ y) → p ▪ p ⁻¹ ≡ refl x
p▪p⁻¹≡reflx {A} {x} {y} = ind≡ (λ x y p → p ▪ p ⁻¹ ≡ refl x)
                               (λ x → refl (refl x)) x y

p⁻¹⁻¹≡p : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
p⁻¹⁻¹≡p {A} {x} {y} = ind≡ (λ x y p → p ⁻¹ ⁻¹ ≡ p)
                           (λ x → refl (refl x)) x y

assoc▪ : {A : Set} {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ w} → p ▪ (q ▪ r) ≡ (p ▪ q) ▪ r
assoc▪ {A} {x} {y} {z} {w} {p} {q} {r} =
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

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ α ⟩ β = α ▪ β 

infix 2 _∎
_∎ : {A : Set} (p : A) → p ≡ p
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

--2.2
--Lemma 2.2.1
ap : {A B : Set} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
ap {A} {B} f {x} {y} p = ind≡ (λ x y p → f x ≡ f y) (λ x → refl (f x)) x y p

--Lemma 2.2.2
ap▪ : {A B : Set} (f : A → B) (x y z : A) →
      (p : x ≡ y) → (q : y ≡ z) →
      ap f (p ▪ q) ≡ ap f p ▪ ap f q
ap▪ {A} {B} f x y z p q =
    ind≡ (λ x y p → (z : A) → (q : y ≡ z) → ap f (p ▪ q) ≡ ap f p ▪ ap f q)
         (λ x z q → ind≡ (λ x z q → ap f (refl x ▪ q) ≡ ap f (refl x) ▪ ap f q)
                         (λ x → refl (refl (f x)))
                         x z q)
         x y p z q

ap⁻¹ : {A B : Set} (f : A → B) (x y : A) →
      (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
ap⁻¹ {A} {B} f x y p =
     ind≡ (λ x y p → ap f (p ⁻¹) ≡ (ap f p) ⁻¹)
          (λ x → refl (refl (f x)))
          x y p

ap∘ : {A B C : Set} (f : A → B) (g : B → C)
      (x y : A) → (p : x ≡ y) →
      ap g (ap f p) ≡ ap (g ∘ f) p
ap∘ {A} {B} {C} f g x y p =
    ind≡ (λ x y p → ap g (ap f p) ≡ ap (g ∘ f) p)
         (λ x → refl (refl (g (f x))))
         x y p

apid : {A B : Set} (x y : A) → (p : x ≡ y) →
       ap id p ≡ p
apid {A} {B} x y p =
     ind≡ (λ x y p → ap id p ≡ p)
          (λ x → refl (refl x))
          x y p

