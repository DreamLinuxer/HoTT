{-# OPTIONS --without-K #-}

module Ch2 where
open import Level using (_⊔_)
open import Ch1

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

infixr 2 _≡⟨_⟩_
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

--2.2
--Lemma 2.2.1
ap : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
ap {ℓ} {ℓ'} {A} {B} f {x} {y} p = ind≡ (λ x y p → f x ≡ f y) (λ x → refl (f x)) x y p

--Lemma 2.2.2
ap▪ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (x y z : A) →
      (p : x ≡ y) → (q : y ≡ z) →
      ap f (p ▪ q) ≡ ap f p ▪ ap f q
ap▪ {ℓ} {ℓ'} {A} {B} f x y z p q =
    ind≡ (λ x y p → (z : A) → (q : y ≡ z) → ap f (p ▪ q) ≡ ap f p ▪ ap f q)
         (λ x z q → ind≡ (λ x z q → ap f (refl x ▪ q) ≡ ap f (refl x) ▪ ap f q)
                         (λ x → refl (refl (f x)))
                         x z q)
         x y p z q

ap⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (x y : A) →
      (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
ap⁻¹ {ℓ} {ℓ'} {A} {B} f x y p =
     ind≡ (λ x y p → ap f (p ⁻¹) ≡ (ap f p) ⁻¹)
          (λ x → refl (refl (f x)))
          x y p

ap∘ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
      (f : A → B) (g : B → C) (x y : A) → (p : x ≡ y) →
      ap g (ap f p) ≡ ap (g ∘ f) p
ap∘ {ℓ} {ℓ'} {ℓ''} {A} {B} {C} f g x y p =
    ind≡ (λ x y p → ap g (ap f p) ≡ ap (g ∘ f) p)
         (λ x → refl (refl (g (f x))))
         x y p

apid : ∀ {ℓ} {A : Set ℓ} (x y : A) → (p : x ≡ y) →
       ap id p ≡ p
apid {ℓ} {A} x y p =
     ind≡ (λ x y p → ap id p ≡ p)
          (λ x → refl (refl x))
          x y p

--2.3
--Lemma 2.3.1
transport : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (p : x ≡ y) → P x → P y
transport {ℓ} {ℓ'} {A} P {x} {y} = ind≡ (λ x y p → P x → P y)
                                   (λ x → id)
                                   x y

_* : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} (p : x ≡ y) → P x → P y
_* {ℓ} {ℓ'} {A} {P} {x} {y} p = transport P p

--Lemma 2.3.2
lift : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (u : P x) (p : x ≡ y) → (x , u) ≡ (y , (p *) u)
lift {ℓ} {ℓ'} {A} P {x} {y} u p = ind≡ (λ x y p → (u : P x) → (x , u) ≡ (y , (_* {P = P} p) u))
                                       (λ x u → refl (x , u))
                                       x y p u

--Lemma 2.3.4
apd : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f : (x : A) → P x)
      {x y : A} (p : x ≡ y) → (p *) (f x) ≡ f y
apd {ℓ} {ℓ'} {A} {P} f {x} {y} = ind≡ (λ x y p → (p *) (f x) ≡ f y)
                                      (λ x → refl (f x))
                                      x y

--Lemma 2.3.5
transportconst : ∀ {ℓ} {ℓ'} {A : Set ℓ} (B : Set ℓ') {x y : A} (p : x ≡ y) →
                 (b : B) → transport (λ x → B) p b ≡ b
transportconst {ℓ} {ℓ'} {A} B {x} {y} =
               ind≡ (λ x y p → (b : B) → transport (λ x → B) p b ≡ b)
                    (λ x b → refl b)
                    x y

--Lemma 2.3.8
apd≡transportconst▪ap : {A B : Set} (f : A → B) {x y : A} (p : x ≡ y) →
                        apd f p ≡ transportconst B p (f x) ▪ ap f p
apd≡transportconst▪ap {A} {B} f {x} {y} =
                      ind≡ (λ x y p → apd f p ≡ transportconst B p (f x) ▪ ap f p)
                           (λ x → refl (refl (f x)))
                           x y

--Lemma 2.3.9
q*[p*[u]]≡[[p▪q]*][u] : {A : Set} (P : A → Set) {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                        (u : P x) → (q *) ((p *) u) ≡ ((p ▪ q) *) u
q*[p*[u]]≡[[p▪q]*][u] {A} P {x} {y} {z} p q u =
                      ind≡ (λ x y p → (z : A) → (q : y ≡ z) → (u : P x) →
                                      (q *) ((p *) u) ≡ (_* {P = P} (p ▪ q)) u)
                           (λ x z q u →
                              ind≡ (λ x z q → (u : P x) →
                                      (q *) ((_* {P = P} (refl x)) u) ≡ ((refl x ▪ q) *) u)
                                   (λ x u → refl u)
                                   x z q u)
                           x y p z q u

--Lemma 2.3.10
transport[P∘f,p,u]≡transport[P,ap[f,p],u] : {A B : Set} (f : A → B) (P : B → Set) {x y : A} (p : x ≡ y) (u : P (f x)) →
                                             transport (P ∘ f) p u ≡ transport P (ap f p) u
transport[P∘f,p,u]≡transport[P,ap[f,p],u] {A} {B} f P {x} {y} p u =
                                          ind≡ (λ x y p → (u : P (f x))
                                                  → transport (P ∘ f) p u ≡ transport P (ap f p) u)
                                               (λ x u → refl u)
                                               x y p u

--Lemma 2.3.11
transport[Q,p,f[x,u]]≡f[y,transport[P,p,u]] : {A : Set} (P Q : A → Set) (f : (x : A) → P x → Q x) →
                                              {x y : A} (p : x ≡ y) (u : P x) →
                                              transport Q p (f x u) ≡ f y (transport P p u)
transport[Q,p,f[x,u]]≡f[y,transport[P,p,u]] {A} P Q f {x} {y} p u =
                                            ind≡ (λ x y p → (u : P x)
                                                    → transport Q p (f x u) ≡ f y (transport P p u))
                                                 (λ x u → refl (f x u))
                                                 x y p u

--2.4
infix 2 _~_

_~_ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_~_ {A = A} f g = (x : A) → f x ≡ g x

--Lemma 2.4.2
ref~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → f ~ f
ref~ f = λ x → ap f (refl x)

sym~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → f ~ g → g ~ f
sym~ {ℓ} {ℓ'} {A} {B} {f} {g} f~g = λ x → (f~g x) ⁻¹

tran~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g h : A → B} → f ~ g → g ~ h → f ~ h
tran~ {ℓ} {ℓ'} {A} {B} {f} {g} {h} f~g g~h = λ x → (f~g x) ▪ (g~h x)

--Lemma 2.4.3
ntran~ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f g : A → B) (H : f ~ g) {x y : A} (p : x ≡ y) →
         H x ▪ ap g p ≡ ap f p ▪ H y
ntran~ {ℓ} {ℓ'} {A} {B} f g H {x} {y} p = ind≡ (λ x y p → H x ▪ ap g p ≡ ap f p ▪ H y)
                                               (λ x → ((unit-right (H x)) ⁻¹) ▪ (unit-left (H x)))
                                               x y p

--Corollary 2.4.4
comm~' : ∀ {ℓ} {A : Set ℓ} (f : A → A) (H : f ~ id) (x : A) →
         H (f x) ▪ H x ≡ ap f (H x) ▪ H x
comm~' {ℓ} {A} f H x = (H (f x) ▪ H x)
                     ≡⟨ ap (λ p → H (f x) ▪ p) (apid (f x) x (H x) ⁻¹) ⟩
                       H (f x) ▪ ap id (H x)
                     ≡⟨ ntran~ f id H (H x) ⟩
                       (ap f (H x) ▪ H x ∎)

comm~ : ∀ {ℓ} {A : Set ℓ} (f : A → A) (H : f ~ id) (x : A) →
        H (f x) ≡ ap f (H x)
comm~ {ℓ} {A} f H x = H (f x)
                    ≡⟨ unit-right (H (f x)) ⟩
                      H (f x) ▪ refl (f x)
                    ≡⟨ ap (λ p → H (f x) ▪ p) (p▪p⁻¹≡reflx (H x)) ⁻¹ ⟩
                      H (f x) ▪ (H x ▪ H x ⁻¹)
                    ≡⟨ assoc▪ (H (f x)) (H x) (H x ⁻¹)⟩
                      H (f x) ▪ H x ▪ H x ⁻¹
                    ≡⟨ ap (λ p → p ▪ H x ⁻¹) (comm~' f H x) ⟩
                      ap f (H x) ▪ H x ▪ H x ⁻¹
                    ≡⟨ assoc▪ (ap f (H x)) (H x) (H x ⁻¹) ⁻¹ ⟩
                      ap f (H x) ▪ (H x ▪ H x ⁻¹)
                    ≡⟨ ap (λ p → ap f (H x) ▪ p) (p▪p⁻¹≡reflx (H x)) ⟩
                      ap f (H x) ▪ refl (f x)
                    ≡⟨ unit-right (ap f (H x)) ⁻¹ ⟩
                      ap f (H x) ∎

--Definition 2.4.6
qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
qinv {ℓ} {ℓ'} {A} {B} f = Σ[ g ∈ (B → A) ] (f ∘ g ~ id) × (g ∘ f ~ id)

--Example 2.4.7
qinvId : {A : Set} → qinv {A = A} id
qinvId = id , ((λ y → refl y) , (λ x → refl x))

--Example 2.4.8
qinv≡₁ : {A : Set} {x y : A} (p : x ≡ y) (z : A) → qinv {A = y ≡ z} {B = x ≡ z} (λ q → p ▪ q)
qinv≡₁ {A} {x} {y} p z = (λ q → p ⁻¹ ▪ q)
                       , ( (λ q → p ▪ (p ⁻¹ ▪ q)
                                ≡⟨ assoc▪ p (p ⁻¹) q ⟩
                                  p ▪ p ⁻¹ ▪ q
                                ≡⟨ ap (λ p → p ▪ q) (p▪p⁻¹≡reflx p) ⟩
                                  refl x ▪ q
                                ≡⟨ (unit-left q) ⁻¹ ⟩
                                  q ∎)
                         , (λ q → p ⁻¹ ▪ (p ▪ q)
                                ≡⟨ assoc▪ (p ⁻¹) p q ⟩
                                  p ⁻¹ ▪ p ▪ q
                                ≡⟨ ap (λ p₁ → p₁ ▪ q) (p⁻¹▪p≡refly p) ⟩
                                  refl y ▪ q
                                ≡⟨ (unit-left q) ⁻¹ ⟩
                                   q ∎))

qinv≡₂ : {A : Set} {x y : A} (p : x ≡ y) (z : A) → qinv {A = z ≡ x} {B = z ≡ y} (λ q → q ▪ p)
qinv≡₂ {A} {x} {y} p z = (λ q → q ▪ p ⁻¹)
                       , ( (λ q → q ▪ p ⁻¹ ▪ p
                                ≡⟨ (assoc▪ q (p ⁻¹) p) ⁻¹ ⟩
                                  q ▪ (p ⁻¹ ▪ p)
                                ≡⟨ ap (λ p → q ▪ p) (p⁻¹▪p≡refly p) ⟩
                                  q ▪ refl y
                                ≡⟨ (unit-right q) ⁻¹ ⟩
                                   q ∎)
                         , (λ q → q ▪ p ▪ p ⁻¹
                                ≡⟨ (assoc▪ q p (p ⁻¹)) ⁻¹ ⟩
                                   q ▪ (p ▪ p ⁻¹)
                                ≡⟨ ap (λ p → q ▪ p) (p▪p⁻¹≡reflx p) ⟩
                                   q ▪ refl x
                                ≡⟨ (unit-right q) ⁻¹ ⟩
                                   q ∎))

qinv≡₃ : {A : Set} {x y : A} (P : A → Set) (p : x ≡ y) →
         qinv {A = P x} {B = P y} (transport P p)
qinv≡₃ {A} {x} {y} P p = (transport P (p ⁻¹))
                       , ((λ z → (p *) ((p ⁻¹ *) z)
                               ≡⟨ q*[p*[u]]≡[[p▪q]*][u] P (p ⁻¹) p z ⟩
                                 ((p ⁻¹ ▪ p) *) z
                               ≡⟨ ap (λ p → (p *) z) (p⁻¹▪p≡refly p) ⟩
                                 z ∎)
                       ,  (λ z → ((p ⁻¹) *) ((p *) z)
                               ≡⟨ q*[p*[u]]≡[[p▪q]*][u] P p (p ⁻¹) z ⟩
                                 ((p ▪ p ⁻¹) *) z
                               ≡⟨ ap (λ p → (p *) z) (p▪p⁻¹≡reflx p) ⟩
                                 z ∎))

isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
isequiv {ℓ} {ℓ'} {A} {B} f = (Σ[ g ∈ (B → A) ] (f ∘ g ~ id) ) × (Σ[ h ∈ (B → A) ] (h ∘ f ~ id) )

qinv→isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               qinv f → isequiv f
qinv→isequiv (g , (α , β))= (g , α) , (g , β)

isequiv→qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               isequiv f → qinv f
isequiv→qinv {f = f} ((g , α) , (h , β)) =
             let γ : g ~ h
                 γ x = (β (g x) ⁻¹) ▪ (ap h (α x))
             in  g , (α , (λ x → (γ (f x)) ▪ (β x)))

_≃_ : ∀ {ℓ} {ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

--Lemma 2.4.12
ref≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
ref≃ = id , ((id , refl) , (id , refl))

sym≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
sym≃ (f , eq) with (isequiv→qinv eq)
sym≃ (f , eq) | (f⁻¹ , (α , β)) = f⁻¹ , ((f , β) , (f , α))

tran≃ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
        A ≃ B → B ≃ C → A ≃ C
tran≃ (f , eq1) (g , eq2) with (isequiv→qinv eq1)
tran≃ (f , eq1) (g , eq2) | (f⁻¹ , (α1 , β1)) with (isequiv→qinv eq2)
tran≃ (f , eq1) (g , eq2) | (f⁻¹ , (α1 , β1)) | (g⁻¹ , (α2 , β2)) =
      (g ∘ f) , ((f⁻¹ ∘ g⁻¹ , (λ x → g (f (f⁻¹ (g⁻¹ x)))
                                   ≡⟨ ap (λ y → g y) (α1 (g⁻¹ x)) ⟩
                                     g (g⁻¹ x)
                                   ≡⟨ α2 x ⟩
                                     x ∎))
              ,  (f⁻¹ ∘ g⁻¹ , (λ x → f⁻¹ (g⁻¹ (g (f x)))
                                   ≡⟨ ap (λ y → f⁻¹ y) (β2 (f x)) ⟩
                                     f⁻¹ (f x)
                                   ≡⟨ β1 x ⟩
                                     x ∎)))

-- 2.6
pair×≡⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
           (x ≡ y) → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)
pair×≡⁻¹ p = (ap pr₁ p) , (ap pr₂ p)

pair×≡' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a a' : A} {b b' : B} →
          (a ≡ a') × (b ≡ b') → (a , b) ≡ (a' , b')
pair×≡' {ℓ} {ℓ'} {A} {B} {a} {a'} {b} {b'} =
       rec× ((a , b) ≡ (a' , b'))
            (λ p q → ind≡ (λ a a' p → a , b ≡ a' , b')
                          (ind≡ (λ b b' q → (x : A) → x , b ≡ x , b')
                                (λ b a → refl (a , b))
                                b b' q)
                          a a' p)

pair×≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
         (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y) → (x ≡ y)
pair×≡ {ℓ} {ℓ'} {A} {B} {a , b} {a' , b'} = pair×≡' {ℓ} {ℓ'} {A} {B} {a} {a'} {b} {b'}

--Theorem 2.6.2
×≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
     isequiv (pair×≡⁻¹ {ℓ} {ℓ'} {A} {B} {x} {y})
×≃ {ℓ} {ℓ'} {A} {B} {x} {y} =
   qinv→isequiv
   ( pair×≡
   , ((λ s → ind× (λ x → (y : A × B)
                       → (s : (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y))
                       → (pair×≡⁻¹ ∘ (pair×≡ {x = x} {y = y})) s ≡ s)
                  (λ a b y s →
                     ind× (λ y → (s : (a ≡ pr₁ y) × (b ≡ pr₂ y))
                               → (pair×≡⁻¹ ∘ (pair×≡ {x = (a , b)} {y = y})) s ≡ s)
                          (λ a' b' → ind× (λ s → (pair×≡⁻¹ ∘ pair×≡ {x = a , b} {y = a' , b'}) s ≡ s)
                                          (λ p q → ind≡ (λ a a' p → (pair×≡⁻¹ ∘ pair×≡') (p , q) ≡ p , q)
                                                        (λ a → ind≡ (λ b b' q → (pair×≡⁻¹ ∘ pair×≡') (refl a , q) ≡ refl a , q)
                                                                    (λ b → refl (refl a , refl b))
                                                                    b b' q)
                                                        a a' p))
                                          y s)
                          x y s)
   ,  (λ r → ind≡ (λ x y r → (pair×≡ ∘ pair×≡⁻¹) r ≡ r)
                  (λ x → ind× (λ x → (pair×≡ ∘ pair×≡⁻¹) (refl x) ≡ refl x)
                              (λ a b → refl (refl (a , b)))
                              x)
                  x y r)))

uppt× : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (z : A × B) → ((pr₁ z , pr₂ z) ≡ z)
uppt× z = pair×≡ ((refl (pr₁ z)) , (refl (pr₂ z)))

--Theorem 2.6.4
transport× : ∀ {ℓ ℓ' ℓ''} {Z : Set ℓ} {A : Z → Set ℓ'} {B : Z → Set ℓ''}
             {z w : Z} (p : z ≡ w) (x : A z × B z) →
             transport (λ z → A z × B z) p x ≡ (transport (λ z → A z) p (pr₁ x) , transport (λ z → B z) p (pr₂ x))
transport× {ℓ} {ℓ'} {ℓ''} {Z} {A} {B} {z} {w} p x =
           ind≡ (λ z w p → (x : A z × B z) →
                           transport (λ z → A z × B z) p x ≡ transport (λ z → A z) p (pr₁ x) , transport (λ z → B z) p (pr₂ x))
                (λ z x → (uppt× x) ⁻¹)
                z w p x

--Theorem 2.6.5
ap× : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {A' : Set ℓ₃} {B' : Set ℓ₄} →
      (g : A → A') (h : B → B') (x y : A × B) (p : pr₁ x ≡ pr₁ y) (q : pr₂ x ≡ pr₂ y) →
      (ap (λ x → (g (pr₁ x) , h (pr₂ x))) (pair×≡ {x = x} {y = y} (p , q))) ≡ (pair×≡ (ap g p , ap h q))
ap× {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {A} {B} {A'} {B'} g h (a , b) (a' , b') p q =
    ind≡ (λ a a' p → (q : b ≡ b') →
            ap (λ x → g (pr₁ x) , h (pr₂ x))
               (pair×≡ {x = (a , b)} {y = (a' , b')} (p , q))
            ≡
            pair×≡ (ap g p , ap h q))
         (λ a q → ind≡ (λ b b' q →
                          ap (λ x → g (pr₁ x) , h (pr₂ x))
                             (pair×≡ {x = (a , b)} {y = (a , b')} (refl a , q))
                          ≡
                          pair×≡ (ap g (refl a) , ap h q))
                       (λ b → refl (refl (g a , h b)))
                       b b' q)
         a a' p q

--2.7
--Theorem 2.7.2
Σ≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
     (w ≡ w') ≃ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
Σ≃ {ℓ} {ℓ'} {A} {P} {w} {w'} =
    let f : {w w' : Σ[ x ∈ A ] P x} → (w ≡ w') → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
        f {w} {w'} = ind≡ (λ w w' p → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))))
                          (λ w → refl (pr₁ w) , refl (pr₂ w))
                          w w'
                          
        g : {w w' : Σ[ x ∈ A ] P x} → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))) → w ≡ w'
        g {w} {w'} = indΣ (λ w → (w' : Σ[ x ∈ A ] P x)
                               → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))) → w ≡ w')
                          (λ w₁ w₂ w' →
                             indΣ (λ w' → (Σ[ p ∈ (w₁ ≡ pr₁ w') ] ((_* {P = P} p) w₂ ≡ (pr₂ w'))) → (w₁ , w₂) ≡ w')
                                  (λ w₁' w₂' →
                                     indΣ (λ _ → w₁ , w₂ ≡ w₁' , w₂')
                                          (λ p q →
                                             ind≡ (λ w₁ w₁' p → (w₂ : P w₁) → (w₂' : P w₁')
                                                              → (p *) w₂ ≡ w₂' → (w₁ , w₂ ≡ w₁' , w₂'))
                                                  (λ w₁ w₂ w₂' q →
                                                     ind≡ (λ w₂ w₂' q → w₁ , w₂ ≡ w₁ , w₂')
                                                          (λ w₂ → refl (w₁ , w₂))
                                                          w₂ w₂' q)
                                                  w₁ w₁' p w₂ w₂' q))
                                  w')
                          w w'
                          
        f∘g~id : {w w' : Σ[ x ∈ A ] P x} → (f {w} {w'}) ∘ g ~ id
        f∘g~id {w} {w'} r = indΣ (λ w → (w' : Σ[ x ∈ A ] P x)
                                      → (r : Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
                                      → f {w} {w'} (g r) ≡ r)
                                 (λ w₁ w₂ w' r →
                                    indΣ (λ w' → (r : Σ[ p ∈ (w₁ ≡ pr₁ w') ] ((_* {P = P} p) w₂ ≡ (pr₂ w')))
                                               → f {w₁ , w₂} {w'} (g r) ≡ r)
                                         (λ w₁' w₂' r →
                                            indΣ (λ r → f {w₁ , w₂} {w₁' , w₂'} (g r) ≡ r)
                                                 (λ p q →
                                                    ind≡ (λ w₁ w₁' p → (w₂ : P w₁) → (w₂' : P w₁')
                                                                     → (q : (p *) w₂ ≡ w₂')
                                                                     → f {w₁ , w₂} {w₁' , w₂'} (g (p , q)) ≡ (p , q))
                                                         (λ w₁ w₂ w₂' q →
                                                            ind≡ (λ w₂ w₂' q → f {w₁ , w₂} {w₁ , w₂'} (g (refl w₁ , q)) ≡ (refl w₁ , q))
                                                                 (λ w₂ → refl (refl w₁ , refl w₂))
                                                                 w₂ w₂' q)
                                                         w₁ w₁' p w₂ w₂' q)
                                                 r)
                                         w' r)
                                 w w' r
                                 
        g∘f~id : {w w' : Σ[ x ∈ A ] P x} → (g {w} {w'}) ∘ f ~ id
        g∘f~id {w} {w'} p = ind≡ (λ w w' p → g {w} {w'} (f p) ≡ p)
                                 (indΣ (λ w → g (f (refl w)) ≡ refl w)
                                       (λ w₁ w₂ → refl (refl (w₁ , w₂))))
                                 w w' p
    in  f , qinv→isequiv (g , (f∘g~id {w} {w'} , g∘f~id))

--Corollary 2.7.3
upptΣ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} → (z : Σ[ x ∈ A ] P x) → z ≡ (pr₁ z , pr₂ z)
upptΣ {ℓ} {ℓ'} {A} {P} z with Σ≃ {w = z} {w' = (pr₁ z , pr₂ z)}
upptΣ z | f , ((g , α) , (h , β)) = g (refl (pr₁ z) , refl (pr₂ z))

pairΣ≡⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
           (w ≡ w') → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
pairΣ≡⁻¹ {w = w} {w' = w'} with Σ≃ {w = w} {w' = w'}
pairΣ≡⁻¹ | f , ((g , α) , (h , β)) = f

pairΣ≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
         (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))) → w ≡ w'
pairΣ≡ {w = w} {w' = w'} with Σ≃ {w = w} {w' = w'}
pairΣ≡ | f , ((g , α) , (h , β)) = g

--Theorem 2.7.4
liftΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : (Σ[ x ∈ A ] (P x)) → Set ℓ''} →
        {x y : A} (p : x ≡ y) (u : P x) (z : Q (x , u)) →
        _* {P = λ x → Σ[ u ∈ (P x) ] (Q (x , u))} p (u , z)
        ≡
        ((p *) u , _* {P = Q} (pairΣ≡ (p , refl ((p *) u))) z)
liftΣ {ℓ} {ℓ'} {ℓ''} {A} {P} {Q} {x} {y} p u z =
      ind≡ (λ x y p → (u : P x) → (z : Q (x , u))
                    → _* {P = λ x → Σ[ u ∈ (P x) ] (Q (x , u))} p (u , z)
                    ≡ ((p *) u , _* {P = Q} (pairΣ≡ (p , refl ((p *) u))) z))
           (λ x u z → refl (u , z))
           x y p u z

--2.8
𝟙≡⁻¹ : {x y : 𝟙} → (x ≡ y) → 𝟙
𝟙≡⁻¹ = (λ _ → ⊤)

𝟙≡ : {x y : 𝟙} → 𝟙 → (x ≡ y)
𝟙≡ {x} {y} = (λ z → ind𝟙 (λ z → (x y : 𝟙) → x ≡ y)
                         (λ x y → ind𝟙 (λ x → (y : 𝟙) → x ≡ y)
                                       (λ y → ind𝟙 (λ y → ⊤ ≡ y) (refl ⊤) y)
                                       x y)
                         z x y)

--Theorem 2.8.1
𝟙≃ : {x y : 𝟙} → (x ≡ y) ≃ 𝟙
𝟙≃ {x} {y} = 𝟙≡⁻¹ , qinv→isequiv (𝟙≡ , ( (λ u → ind𝟙 (λ u → (𝟙≡⁻¹ {x = x} {y = y} ∘ 𝟙≡) u ≡ u)
                                                     (refl ⊤)
                                                     u)
                                       , (λ p → ind≡ (λ x y p → (𝟙≡ ∘ 𝟙≡⁻¹) p ≡ p)
                                                     (ind𝟙 (λ x → (𝟙≡ ∘ 𝟙≡⁻¹) (refl x) ≡ refl x)
                                                           (refl (refl ⊤)))
                                                     x y p)))
                                                     
uppt𝟙 : (u : 𝟙) → u ≡ ⊤
uppt𝟙 = ind𝟙 (λ u → u ≡ ⊤) (refl ⊤)
