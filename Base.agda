{-# OPTIONS --without-K #-}

module Base where
open import Level using (_⊔_)

id : ∀ {ℓ} {A : Set ℓ} → A → A
id a = a

infix 4 _≡_
data _≡_ {ℓ} {A : Set ℓ} : (x y : A) → Set ℓ where
  refl : (x : A) → x ≡ x

infix 5 _,_
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁

infix 2 Σ-syntax
open Σ

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

recΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} → (C : Set ℓ'') →
       (g : (a : A) (b : B a) → C) → Σ A B → C
recΣ C g (a , b) = g a b

indΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} → (C : Σ A B → Set ℓ'') →
       (g : (a : A) (b : B a) → C (a , b)) → (p : Σ A B) → C p
indΣ C g (a , b) = g a b

rec× : ∀ {α β γ} {A : Set α} {B : Set β} (C : Set γ) →
       (A → B → C) → A × B → C
rec× C g (a , b)= g a b

ind× : ∀ {α β γ} {A : Set α} {B : Set β} (C : A × B → Set γ) →
       ((x : A) (y : B) → C (x , y)) → (x : A × B) → C x
ind× C g (a , b) = g a b

data 𝟙 : Set where
  ⊤ : 𝟙

rec𝟙 : ∀ {ℓ} (C : Set ℓ) → C → 𝟙 → C
rec𝟙 C c ⊤ = c

ind𝟙 : ∀ {ℓ} (C : 𝟙 → Set ℓ) → C ⊤ → ((x : 𝟙) → C x)
ind𝟙 C c ⊤ = c

data 𝟘 : Set where

rec𝟘 : ∀ {ℓ} (C : Set ℓ) → 𝟘 → C
rec𝟘 C ()

ind𝟘 : ∀ {ℓ} (C : 𝟘 → Set ℓ) → (z : 𝟘) → C z
ind𝟘 C ()

data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (x : A) → A + B
  inr : (y : B) → A + B

rec+ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (C : Set ℓ'') →
       (A → C) → (B → C) → A + B → C
rec+ C g₀ g₁ (inl a) = g₀ a
rec+ C g₀ g₁ (inr b) = g₁ b

ind+ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (C : A + B → Set ℓ'') →
       ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
ind+ C g₀ g₁ (inl a) = g₀ a
ind+ C g₀ g₁ (inr b) = g₁ b

data ℕ : Set where
  zero : ℕ
  succ  : ℕ → ℕ

recℕ : ∀ {ℓ} (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
recℕ C c₀ cs zero = c₀
recℕ C c₀ cs (succ n) = cs n (recℕ C c₀ cs n)

indℕ : ∀ {ℓ} (C : ℕ → Set ℓ) → C zero → ((n : ℕ) → C n → C (succ n)) → (n : ℕ) → C n
indℕ C c₀ cs zero = c₀
indℕ C c₀ cs (succ n) = cs n (indℕ C c₀ cs n)

¬_ : ∀ {ℓ} (A : Set ℓ) → Set ℓ
¬_ {ℓ} A = A → 𝟘

ind≡ : ∀ {ℓ ℓ'} {A : Set ℓ} (C : (x y : A) (p : x ≡ y) → Set ℓ') →
       ((x : A) → C x x (refl x)) →
       ((x y : A) (p : x ≡ y) → C x y p)
ind≡ C c x .x (refl .x) = c x

ind≡' : ∀ {ℓ ℓ'} {A : Set ℓ} (a : A) (C : (x : A) (p : a ≡ x) → Set ℓ') →
        (C a (refl a)) →
        ((x : A) (p : a ≡ x) → C x p)
ind≡' a C c .a (refl .a) = c

_≠_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≠ y = ¬ (x ≡ y)

infixr 20 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (g : B → C) → (f : A → B) → (A → C)
_∘_ g f = (λ x → g (f x))

--Lemma 2.1.1
infix 21 _⁻¹
_⁻¹ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
refl x ⁻¹ = refl x

--Lemma 2.1.2
infixl 10 _▪_
_▪_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl x ▪ refl .x = refl x 

--Lemma 2.1.4
unit-right : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ≡ p ▪ (refl y)
unit-right (refl x) = refl (refl x)

unit-left : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ≡ (refl x) ▪ p
unit-left (refl x) = refl (refl x)

p⁻¹▪p≡refly : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⁻¹ ▪ p ≡ refl y
p⁻¹▪p≡refly (refl x) = refl (refl x)

p▪p⁻¹≡reflx : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ▪ p ⁻¹ ≡ refl x
p▪p⁻¹≡reflx (refl x) = refl (refl x)

p⁻¹⁻¹≡p : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
p⁻¹⁻¹≡p (refl x) = refl (refl x)

assoc▪ : ∀ {ℓ} {A : Set ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ▪ (q ▪ r) ≡ (p ▪ q) ▪ r
assoc▪ (refl x) (refl .x) (refl .x) = refl (refl x)

infixr 1 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ α ⟩ β = α ▪ β

infix 2 _∎
_∎ : ∀ {ℓ} {A : Set ℓ} (p : A) → p ≡ p
p ∎ = refl p

--Lemma 2.2.1
ap : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

--Lemma 2.2.2
ap▪ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (x y z : A) →
      (p : x ≡ y) → (q : y ≡ z) →
      ap f (p ▪ q) ≡ ap f p ▪ ap f q
ap▪ f x .x .x (refl .x) (refl .x) = refl (refl (f x))

ap⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (x y : A) →
       (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
ap⁻¹ f x .x (refl .x) = refl (refl (f x))

ap∘ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
      (f : A → B) (g : B → C) (x y : A) → (p : x ≡ y) →
      ap g (ap f p) ≡ ap (g ∘ f) p
ap∘ f g x .x (refl .x) = refl (refl (g (f x)))

apid : ∀ {ℓ} {A : Set ℓ} (x y : A) → (p : x ≡ y) →
       ap id p ≡ p
apid x .x (refl .x) = refl (refl x)

--Lemma 2.3.1
transport : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (p : x ≡ y) → P x → P y
transport P (refl x) p = p

_* : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} (p : x ≡ y) → P x → P y
_* {P = P} p = transport P p 

--Lemma 2.3.2
lift : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (u : P x) (p : x ≡ y) → (x , u) ≡ (y , (_* {P = P} p) u)
lift P u (refl x) = refl (x , u)

--Lemma 2.3.4
apd : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f : (x : A) → P x)
      {x y : A} (p : x ≡ y) → (p *) (f x) ≡ f y
apd f (refl x) = refl (f x)

infix 2 _~_

_~_ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_~_ {A = A} f g = (x : A) → f x ≡ g x

--Lemma 2.4.2
ref~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → f ~ f
ref~ f = λ x → refl (f x)

sym~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → f ~ g → g ~ f
sym~ {ℓ} {ℓ'} {A} {B} {f} {g} f~g = λ x → (f~g x) ⁻¹

tran~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g h : A → B} → f ~ g → g ~ h → f ~ h
tran~ {ℓ} {ℓ'} {A} {B} {f} {g} {h} f~g g~h = λ x → (f~g x) ▪ (g~h x)

--Lemma 2.4.3
ntran~ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f g : A → B) (H : f ~ g) {x y : A} (p : x ≡ y) →
         H x ▪ ap g p ≡ ap f p ▪ H y
ntran~ f g H (refl x) = (unit-right (H x))⁻¹ ▪ unit-left (H x)

record qinv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkqinv
  field
    g : B → A 
    α : (f ∘ g) ~ id
    β : (g ∘ f) ~ id

record isequiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : 
  Set (ℓ ⊔ ℓ') where
  constructor mkisequiv
  field
    g : B → A 
    α : (f ∘ g) ~ id
    h : B → A
    β : (h ∘ f) ~ id

qinv→isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               qinv f → isequiv f
qinv→isequiv (mkqinv g α β) = mkisequiv g α g β

isequiv→qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               isequiv f → qinv f
isequiv→qinv {f = f} (mkisequiv g α h β) =
             let γ : g ~ h
                 γ x = (β (g x) ⁻¹) ▪ (ap h (α x))
             in  mkqinv g α (λ x → (γ (f x)) ▪ (β x))

infix 2 _≃_
_≃_ : ∀ {ℓ} {ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

--Lemma 2.4.12
ref≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
ref≃ = id , (mkisequiv id refl id refl)

sym≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
sym≃ (f , eq) with (isequiv→qinv eq)
sym≃ (f , eq) | (mkqinv f⁻¹ α β) = f⁻¹ , (mkisequiv f β f α)

tran≃ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
        A ≃ B → B ≃ C → A ≃ C
tran≃ (f , eq1) (g , eq2) with (isequiv→qinv eq1)
tran≃ (f , eq1) (g , eq2) | (mkqinv f⁻¹ α1 β1) with (isequiv→qinv eq2)
tran≃ (f , eq1) (g , eq2) | (mkqinv f⁻¹ α1 β1) | (mkqinv g⁻¹ α2 β2) =
      (g ∘ f) ,
      mkisequiv (f⁻¹ ∘ g⁻¹)
                (λ x → g (f (f⁻¹ (g⁻¹ x)))
                    ≡⟨ ap (λ y → g y) (α1 (g⁻¹ x)) ⟩
                       g (g⁻¹ x)
                    ≡⟨ α2 x ⟩
                       x ∎)
                (f⁻¹ ∘ g⁻¹)
                (λ x → f⁻¹ (g⁻¹ (g (f x)))
                    ≡⟨ ap (λ y → f⁻¹ y) (β2 (f x)) ⟩
                       f⁻¹ (f x)
                    ≡⟨ β1 x ⟩
                       x ∎)

infix 3 _○_
_○_ : ∀ {ℓ} {ℓ'} {ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
      (f : B ≃ C) (g : A ≃ B) → A ≃ C
g ○ f  = tran≃ f g

infix 20 _⁻¹≃
_⁻¹≃ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A ≃ B) → B ≃ A
_⁻¹≃ f = sym≃ f
