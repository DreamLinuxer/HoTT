{-# OPTIONS --without-K #-}

module Ch2-3 where
open import Ch2-2 public

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
apd≡transportconst▪ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) {x y : A} (p : x ≡ y) →
                        apd f p ≡ transportconst B p (f x) ▪ ap f p
apd≡transportconst▪ap {ℓ} {ℓ'} {A} {B} f {x} {y} =
                      ind≡ (λ x y p → apd f p ≡ transportconst B p (f x) ▪ ap f p)
                           (λ x → refl (refl (f x)))
                           x y

--Lemma 2.3.9
q*[p*[u]]≡[[p▪q]*][u] : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                        (u : P x) → (q *) ((p *) u) ≡ ((p ▪ q) *) u
q*[p*[u]]≡[[p▪q]*][u] {ℓ} {ℓ'} {A} P {x} {y} {z} p q u =
                      ind≡ (λ x y p → (z : A) → (q : y ≡ z) → (u : P x) →
                                      (q *) ((p *) u) ≡ (_* {P = P} (p ▪ q)) u)
                           (λ x z q u →
                              ind≡ (λ x z q → (u : P x) →
                                      (q *) ((_* {P = P} (refl x)) u) ≡ ((refl x ▪ q) *) u)
                                   (λ x u → refl u)
                                   x z q u)
                           x y p z q u

--Lemma 2.3.10
transport[P∘f,p,u]≡transport[P,ap[f,p],u] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (P : B → Set ℓ'')
                                            {x y : A} (p : x ≡ y) (u : P (f x)) →
                                            transport (P ∘ f) p u ≡ transport P (ap f p) u
transport[P∘f,p,u]≡transport[P,ap[f,p],u] {ℓ} {ℓ'} {A} {B} f P {x} {y} p u =
                                          ind≡ (λ x y p → (u : P (f x))
                                                  → transport (P ∘ f) p u ≡ transport P (ap f p) u)
                                               (λ x u → refl u)
                                               x y p u

--Lemma 2.3.11
transport[Q,p,f[x,u]]≡f[y,transport[P,p,u]] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} (P : A → Set ℓ') (Q : A → Set ℓ'') →
                                              (f : (x : A) → P x → Q x) →
                                              {x y : A} (p : x ≡ y) (u : P x) →
                                              transport Q p (f x u) ≡ f y (transport P p u)
transport[Q,p,f[x,u]]≡f[y,transport[P,p,u]] {ℓ} {ℓ'} {ℓ''} {A} P Q f {x} {y} p u =
                                            ind≡ (λ x y p → (u : P x)
                                                    → transport Q p (f x u) ≡ f y (transport P p u))
                                                 (λ x u → refl (f x u))
                                                 x y p u
