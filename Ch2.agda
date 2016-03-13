{-# OPTIONS --without-K #-}

module Ch2 where
open import Level using (_⊔_)
open import Ch1

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (g : B → C) → (f : A → B) → (A → C)
_∘_ g f = (λ x → g (f x))

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

assoc▪ : {A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ▪ (q ▪ r) ≡ (p ▪ q) ▪ r
assoc▪ {A} {x} {y} {z} {w} p q r =
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

apid : {A : Set} (x y : A) → (p : x ≡ y) →
       ap id p ≡ p
apid {A} x y p =
     ind≡ (λ x y p → ap id p ≡ p)
          (λ x → refl (refl x))
          x y p

--2.3
--Lemma 2.3.1
transport : {A : Set} (P : A → Set) {x y : A} (p : x ≡ y) → P x → P y
transport {A} P {x} {y} = ind≡ (λ x y p → P x → P y)
                          (λ x → id)
                          x y

_* : {A : Set} {P : A → Set} {x y : A} (p : x ≡ y) → P x → P y
_* {A} {P} {x} {y} p = transport P p

--Lemma 2.3.2
lift : {A : Set} (P : A → Set) {x y : A} (u : P x) (p : x ≡ y) → (x , u) ≡ (y , (p *) u)
lift {A} P {x} {y} u p = ind≡ (λ x y p → (u : P x) → (x , u) ≡ (y , (_* {P = P} p) u))
                          (λ x u → refl (x , u))
                          x y p u

--Lemma 2.3.4
apd : {A : Set} {P : A → Set} (f : (x : A) → P x) {x y : A} (p : x ≡ y) →
      (p *) (f x) ≡ f y
apd {A} {P} f {x} {y} = ind≡ (λ x y p → (p *) (f x) ≡ f y)
                        (λ x → refl (f x))
                        x y

--Lemma 2.3.5
transportconst : {A : Set} (B : Set) {x y : A} (p : x ≡ y) →
                 (b : B) → transport (λ x → B) p b ≡ b
transportconst {A} B {x} {y} = ind≡ (λ x y p → (b : B) → transport (λ x → B) p b ≡ b)
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
ref~ : {A B : Set} (f : A → B) → f ~ f
ref~ f = λ x → ap f (refl x)

sym~ : {A B : Set} (f g : A → B) → f ~ g → g ~ f
sym~ f g f~g = λ x → (f~g x) ⁻¹

tran~ : {A B : Set} (f g h : A → B) → f ~ g → g ~ h → f ~ h
tran~ f g h f~g g~h = λ x → (f~g x) ▪ (g~h x)

--Lemma 2.4.3
ntran~ : {A B : Set} (f g : A → B) (H : f ~ g) {x y : A} (p : x ≡ y) →
        H x ▪ ap g p ≡ ap f p ▪ H y
ntran~ {A} {B} f g H {x} {y} p = ind≡ (λ x y p → H x ▪ ap g p ≡ ap f p ▪ H y)
                                      (λ x → ((unit-right (H x)) ⁻¹) ▪ (unit-left (H x)))
                                      x y p
                                      
--Corollary 2.4.4
comm~' : {A : Set} (f : A → A) (H : f ~ id) (x : A) →
         H (f x) ▪ H x ≡ ap f (H x) ▪ H x
comm~' {A} f H x = (H (f x) ▪ H x)
                 ≡⟨ ap (λ p → H (f x) ▪ p) (apid (f x) x (H x) ⁻¹) ⟩
                   H (f x) ▪ ap id (H x)
                 ≡⟨ ntran~ f id H (H x) ⟩
                   (ap f (H x) ▪ H x ∎)

comm~ : {A : Set} (f : A → A) (H : f ~ id) (x : A) →
        H (f x) ≡ ap f (H x)
comm~ {A} f H x = H (f x)
                ≡⟨ unit-right (H (f x)) ⟩
                  H (f x) ▪ refl (f x)
                ≡⟨ ap (λ p → H (f x) ▪ p) (p▪p⁻¹≡reflx (H x)) ⁻¹ ⟩
                   H (f x) ▪ (H x ▪ H x ⁻¹)
                ≡⟨ assoc▪ {A} (H (f x)) (H x) (H x ⁻¹)⟩
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
qinv {ℓ} {ℓ'} {A} {B} f = Σ (B → A) (λ g → (f ∘ g ~ id) × (g ∘ f ~ id))

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
