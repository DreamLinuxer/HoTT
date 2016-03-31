module Ch1 where
open import Level using (_⊔_; suc; zero) public

id : ∀ {ℓ} {A : Set ℓ} → A → A
id a = a

infix 4 _≡_

data _≡_ {ℓ} {A : Set ℓ} : (x y : A) → Set ℓ where
  refl : (x : A) → x ≡ x

swap : (A B C : Set) → (A → B → C) → (B → A → C)
swap A B C g = λ b → λ a → g a b

data Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  _,_ : (x : A) → B x → Σ A B

infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Set ℓ) → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

pr₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → Σ A B → A
pr₁ (a , b) = a

pr₂ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → (p : Σ A B) → B (pr₁ p)
pr₂ (a , b) = b

recΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} → (C : Set ℓ'') →
       (g : (a : A) (b : B a) → C) → Σ A B → C
recΣ C g (a , b) = g a b

indΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} → (C : Σ A B → Set ℓ'') →
       (g : (a : A) (b : B a) → C (a , b)) → (p : Σ A B) → C p
indΣ C g (a , b) = g a b

ac : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {R : A → B → Set ℓ''} →
     ((x : A) → Σ[ y ∈ B ] (R x y)) → (Σ[ f ∈ (A → B) ] ((x : A) → R x (f x)))
ac g = (λ x → pr₁ (g x)) , (λ x → pr₂ (g x))

{-
data _×_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  _,_ : (a : A) → (b : B) → A × B
-}
_×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
_×_ A B = Σ[ x ∈ A ] B

rec× : ∀ {α β γ} {A : Set α} {B : Set β} (C : Set γ) →
       (A → B → C) → A × B → C
rec× C g (a , b)= g a b

ind× : ∀ {α β γ} {A : Set α} {B : Set β} (C : A × B → Set γ) →
       ((x : A) (y : B) → C (x , y)) → (x : A × B) → C x
ind× C g (a , b) = g a b
{-
pr₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A × B → A
pr₁ {A = A} = rec× A (λ a b → a)

pr₂ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A × B → B
pr₂ {B = B} = rec× B (λ a b → b)
-}
uniq× : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (x : A × B) → ((pr₁ x , pr₂ x) ≡ x)
uniq× (a , b) = refl (a , b)

data 𝟙 : Set where
  ⊤ : 𝟙

rec𝟙 : ∀ {ℓ} (C : Set ℓ) → C → 𝟙 → C
rec𝟙 C c ⊤ = c

ind𝟙 : ∀ {ℓ} (C : 𝟙 → Set ℓ) → C ⊤ → ((x : 𝟙) → C x)
ind𝟙 C c ⊤ = c

upun : (x : 𝟙) → x ≡ ⊤
upun = ind𝟙 (λ x → x ≡ ⊤) (refl ⊤)

Magma : Set₁
Magma = Σ[ A ∈ Set ] (A → A → A)

PointedMagma : Set₁
PointedMagma = Σ[ A ∈ Set ] ((A → A → A) × A)

data 𝟘 {ℓ} : Set ℓ where

rec𝟘 : ∀ {ℓ} (C : Set ℓ) → 𝟘 {ℓ} → C
rec𝟘 C ()

ind𝟘 : ∀ {ℓ} (C : 𝟘 → Set ℓ) → (z : 𝟘 {ℓ}) → C z
ind𝟘 C ()

data _+_ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inl : (a : A) → A + B
  inr : (b : B) → A + B

rec+ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (C : Set ℓ'') →
       (A → C) → (B → C) → A + B → C
rec+ C g₀ g₁ (inl a) = g₀ a
rec+ C g₀ g₁ (inr b) = g₁ b

ind+ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (C : A + B → Set ℓ'') →
       ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
ind+ C g₀ g₁ (inl a) = g₀ a
ind+ C g₀ g₁ (inr b) = g₁ b

data 𝟚 : Set where
  0₂ : 𝟚
  1₂ : 𝟚

rec𝟚 : ∀ {ℓ} (C : Set ℓ) → C → C → 𝟚 → C
rec𝟚 C c₀ c₁ 0₂ = c₀
rec𝟚 C c₀ c₁ 1₂ = c₁

ind𝟚 : ∀ {ℓ} (C : 𝟚 → Set ℓ) → C 0₂ → C 1₂ → (x : 𝟚) → C x
ind𝟚 C c₀ c₁ 0₂ = c₀
ind𝟚 C c₀ c₁ 1₂ = c₁

ex𝟚 : (x : 𝟚) → (x ≡ 0₂) + (x ≡ 1₂)
ex𝟚 = ind𝟚 (λ x → (x ≡ 0₂) + (x ≡ 1₂)) (inl (refl 0₂)) (inr (refl 1₂))

_+'_ : (A : Set) (B : Set) → Set
A +' B = Σ[ x ∈ 𝟚 ] rec𝟚 Set A B x

inl' : {A B : Set} → A → A +' B
inl' a = 0₂ , a

inr' : {A B : Set} → B → A +' B
inr' b = 1₂ , b

_×'_ : (A : Set) (B : Set) → Set
A ×' B = (x : 𝟚) → rec𝟚 Set A B x

_,'_ : {A B : Set} → A → B → A ×' B
_,'_ {A} {B} a b = ind𝟚 (rec𝟚 Set A B) a b

data ℕ : Set where
  zeroℕ : ℕ
  succ  : ℕ → ℕ

recℕ : ∀ {ℓ} (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
recℕ C c₀ cs zeroℕ = c₀
recℕ C c₀ cs (succ n) = cs n (recℕ C c₀ cs n)

indℕ : ∀ {ℓ} (C : ℕ → Set ℓ) → C zeroℕ → ((n : ℕ) → C n → C (succ n)) → (n : ℕ) → C n
indℕ C c₀ cs zeroℕ = c₀
indℕ C c₀ cs (succ n) = cs n (indℕ C c₀ cs n)

double : ℕ → ℕ
double = recℕ ℕ zeroℕ (λ n y → succ (succ y))

add : ℕ → ℕ → ℕ
add = recℕ (ℕ → ℕ) (λ n → n) (λ n g m → succ (g m))

postulate
  apℕsucc : {m n : ℕ} → m ≡ n → succ m ≡ succ n

assocℕ : (i j k : ℕ) → add i (add j k) ≡ add (add i j) k
assocℕ = indℕ (λ i → (j k : ℕ) → add i (add j k) ≡ add (add i j) k)
              (λ j k → refl (add j k))
              (λ i h j k → apℕsucc (h j k))

¬_ : ∀ {ℓ} (A : Set ℓ) → Set ℓ
¬_ {ℓ} A = A → 𝟘 {ℓ}

tautology₁ : {A B : Set} → (A → 𝟘) × (B → 𝟘) → (A + B → 𝟘 {zero})
tautology₁ (x , y) = rec+ 𝟘 x y

tautology₂ : {A B : Set} → (A + B → 𝟘 {zero}) → (A → 𝟘) × (B → 𝟘)
tautology₂ f = (λ x → f (inl x)) , (λ x → f (inr x))

tautology₃ : {A : Set} {P Q : A → Set} → ((x : A) → P x × Q x) → ((x : A) → P x) × ((x : A) → Q x)
tautology₃ p = (λ x → pr₁ (p x)) , (λ x → pr₂ (p x))

Semigroup : ∀ {ℓ} → Set (suc ℓ)
Semigroup {ℓ} = Σ[ A ∈ Set ℓ ] (Σ[ m ∈ (A → A → A) ] ((x y z : A) → m x (m y z) ≡ m (m x y) z))

indiscern≡ : ∀ {ℓ ℓ'} {A : Set ℓ} (C : A → Set ℓ') (x y : A) (p : x ≡ y) → C x → C y
indiscern≡ C x .x (refl .x) = id

ind≡ : ∀ {ℓ ℓ'} {A : Set ℓ} (C : (x y : A) (p : x ≡ y) → Set ℓ') →
       ((x : A) → C x x (refl x)) →
       ((x y : A) (p : x ≡ y) → C x y p)
ind≡ C c x .x (refl .x) = c x

ind≡' : ∀ {ℓ ℓ'} {A : Set ℓ} (a : A) (C : (x : A) (p : a ≡ x) → Set ℓ') →
        (C a (refl a)) →
        ((x : A) (p : a ≡ x) → C x p)
ind≡' a C c .a (refl .a) = c

ind≡'→ind≡ : ∀ {ℓ ℓ'} {A : Set ℓ} →
             ((a : A) (C : (x : A) (p : a ≡ x) → Set ℓ') →
              (C a (refl a)) →
              ((x : A) (p : a ≡ x) → C x p)) →
             ((C : (x y : A) (p : x ≡ y) → Set ℓ') →
              ((x : A) → C x x (refl x)) →
              ((x y : A) (p : x ≡ y) → C x y p))
ind≡'→ind≡ ind≡' = λ C c x y p → ind≡' x (C x) (c x) y p

ind≡→ind≡' : ∀ {ℓ ℓ'} {A : Set ℓ} →
             ((C : (x y : A) (p : x ≡ y) → Set (suc ℓ' ⊔ ℓ)) →
              ((x : A) → C x x (refl x)) →
              ((x y : A) (p : x ≡ y) → C x y p)) →
             ((a : A) (C : (x : A) (p : a ≡ x) → Set ℓ') →
              (C a (refl a)) →
              ((x : A) (p : a ≡ x) → C x p))
ind≡→ind≡' {ℓ} {ℓ'} {A} ind≡ =
           λ a C c x p →
           ind≡ (λ x y p → (C : (z : A) → (x ≡ z) → Set ℓ') → C x (refl x) → C y p)
                (λ x C d → d) a x p C c

_≠_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≠ y = ¬ (x ≡ y)
