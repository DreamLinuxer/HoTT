{-# OPTIONS --without-K #-}

module Ex1 where

-- Ex 1.1
module Ex1-1 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  _∘_ : {A B C : Set} (g : B → C) → (f : A → B) → (A → C)
  _∘_ g f = (λ x → g (f x))

  ∘assoc : {A B C D : Set} (f : A → B) (g : B → C) (h : C → D) → (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
  ∘assoc f g h = refl

-- Ex 1.2
module Ex1-2 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
  rec× : {A B : Set} → (C : Set) → (A → B → C) → A × B → C
  rec× C g  = λ p → g (proj₁ p) (proj₂ p)

  rec×≡ : {A B C : Set} → (a : A) → (b : B) → (g : A → B → C) → rec× C g (a , b) ≡ g a b
  rec×≡ a b g = refl 

  recΣ : ∀ {i j k} {A : Set i} {B : A → Set j} → (C : Set k) → ((x : A) → B x → C) → Σ A B → C
  recΣ C f = λ p → f (proj₁ p) (proj₂ p)

  recΣ≡ : {A : Set} {B : A → Set} {C : Set} → (a : A) (b : B a) (g : (x : A) → B x → C) → recΣ C g (a , b) ≡ g a b
  recΣ≡ a b g = refl

-- Ex 1.3
-- require concepts from chapter 2.

-- Ex 1.4
module Ex1-4 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
  open import Data.Nat

  indℕ : ∀ {ℓ} → (C : ℕ → Set ℓ) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
  indℕ C z f 0 = z
  indℕ C z f (suc n) = f n (indℕ C z f n)

  iter : ∀ {ℓ} (C : Set ℓ) → C → (C → C) → ℕ → C
  iter C c₀ cs zero = c₀
  iter C c₀ cs (suc n) = cs (iter C c₀ cs n)

  recℕ : ∀ {ℓ} (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
  recℕ C c₀ cs n = proj₁ (iter (C × ℕ) (c₀ , 0) (λ p → cs (proj₂ p) (proj₁ p) , suc (proj₂ p)) n)

  recℕ≡0 : ∀ {ℓ} (C : Set ℓ) → (c₀ : C) → (cs : (ℕ → C → C)) → recℕ C c₀ cs 0 ≡ c₀
  recℕ≡0 C c₀ cs = refl

  recℕ≡sucn : ∀ {ℓ} (C : Set ℓ) → (c₀ : C) → (cs : (ℕ → C → C)) → (n : ℕ) → recℕ C c₀ cs (suc n) ≡ cs n (recℕ C c₀ cs n)
  recℕ≡sucn C c₀ cs = indℕ (λ n → recℕ C c₀ cs (suc n) ≡ cs n (recℕ C c₀ cs n))
                           refl
                           (λ n p → {!!})

-- Ex 1.5
module Ex1-5 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
  open import Data.Bool
  
  recBool : ∀ {ℓ} → (C : Set ℓ) → C → C → Bool → C
  recBool C el th false = el
  recBool C el th true = th

  indBool : ∀ {ℓ} → (C : Bool → Set ℓ) → C false → C true → (b : Bool) → C b
  indBool C el th false = el
  indBool C el th true = th

  indΣ : ∀ {ℓ₁ ℓ₂ ℓ₃} → {A : Set ℓ₁} {B : A → Set ℓ₂} → (C : Σ A B → Set ℓ₃) → 
         ((a : A) → (b : B a) → C (a , b)) → (p : Σ A B) → C p
  indΣ C g ( a , b ) = g a b

  _+_ : (A : Set) → (B : Set) → Set
  A + B = Σ[ x ∈ Bool ] (recBool Set A B x)

  inl : {A B : Set} → A → A + B
  inl a = false , a

  inr : {A B : Set} → B → A + B
  inr b = true , b

  ind+ : {A : Set} {B : Set} → (C : A + B → Set) → 
          ((a : A) → C (inl a)) → ((b : B) → C (inr b)) →
          ((x : A + B) → C x)
  ind+ {A = A} {B = B} C f g x = indΣ C (indBool (λ b → (y : (recBool Set A B b)) → C (b , y)) f g) x

  indl≡ : {A : Set} {B : Set} → (C : A + B → Set) → 
          (g₀ : (a : A) → C (inl a)) → (g₁ : (b : B) → C (inr b)) → (x : A) →
          ind+ C g₀ g₁ (inl x) ≡ g₀ x
  indl≡ C g₀ g₁ x = refl

  indr≡ : {A : Set} {B : Set} → (C : A + B → Set) → 
          (g₀ : (a : A) → C (inl a)) → (g₁ : (b : B) → C (inr b)) → (x : B) →
          ind+ C g₀ g₁ (inr x) ≡ g₁ x
  indr≡ C g₀ g₁ x = refl

-- Ex 1.6
-- need function extensionality

-- Ex 1.7
-- need concepts from later chapter

-- Ex 1.8
module Ex1-8 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Product
  open import Algebra.Structures
  open import Algebra

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  suc n + m = suc (n + m)

  _*_ : ℕ → ℕ → ℕ
  zero * m = zero
  suc n * m = m + (n * m)

  _^_ : ℕ → ℕ → ℕ
  n ^ zero = suc zero
  n ^ suc m = n * (n ^ m)

  indℕ : ∀ {ℓ} → (C : ℕ → Set ℓ) → C zero → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
  indℕ C z f zero = z
  indℕ C z f (suc n) = f n (indℕ C z f n)

  IsSemiringℕ : IsSemiring _≡_ _+_ _*_ zero (suc zero)
  IsSemiringℕ = record {isSemiringWithoutAnnihilatingZero =
                       record {
                       +-isCommutativeMonoid = {!!} ;
                       *-isMonoid = {!!} ;
                       distrib = {!!} , {!!}} ;
                       zero = (λ n → refl) , indℕ (λ n → n * zero ≡ zero) refl (λ n p → p)}

  Semiringℕ : Semiring _ _
  Semiringℕ = record {Carrier = ℕ
                     ;_≈_ = _≡_
                     ;_+_ = _+_
                     ;_*_ = _*_
                     ;0# = zero
                     ;1# = suc zero
                     ;isSemiring = IsSemiringℕ}

-- Ex 1.9
module Ex1-9 where
  open import Data.Nat

  data Fin : ℕ → Set where
    fzero : {n : ℕ} → Fin (suc n)
    fsuc  : {n : ℕ} → Fin n → Fin (suc n)

  indℕ : ∀ {ℓ} → (C : ℕ → Set ℓ) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
  indℕ C z f 0 = z
  indℕ C z f (suc n) = f n (indℕ C z f n)

  fmax : ∀ n → Fin (suc n)
  fmax n = indℕ (λ n₁ → Fin (suc n₁)) fzero (λ n₁ fn₁ → fsuc fn₁) n

-- Ex 1.10
module Ex1-10 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Nat

  recℕ : ∀ {ℓ} → (C : Set ℓ) → C → (ℕ → C → C) → ℕ → C
  recℕ C z f 0 = z
  recℕ C z f (suc n) = f n (recℕ C z f n)

  ack : ℕ → ℕ → ℕ
  ack = recℕ (ℕ → ℕ) suc (λ m f → recℕ ℕ (f 1) (λ n a → f a))

  ack0n : (n : ℕ) → ack 0 n ≡ suc n
  ack0n n = refl

  ackm0 : (n m : ℕ) → ack (suc m) 0 ≡ ack m 1
  ackm0 n m = refl

  ackmn : (n m : ℕ) → ack (suc m) (suc n) ≡ ack m (ack (suc m) n)
  ackmn n m = refl

-- Ex 1.11
module Ex1-11 where
  open import Relation.Nullary
  
  ¬¬¬A→¬A : {A : Set} → ¬ ¬ ¬ A → ¬ A
  ¬¬¬A→¬A ¬¬¬A A = ¬¬¬A (λ ¬A → ¬A A)

-- Ex 1.12
module Ex1-12 where
  open import Relation.Nullary
  open import Data.Product
  open import Data.Sum
  
  IfAthen[IfBthenA] : {A B : Set} → A → (B → A)
  IfAthen[IfBthenA] = λ a b → a

  IfAthen[notnotA] : {A : Set} → A → ¬ ¬ A
  IfAthen[notnotA] = λ A ¬A → ¬A A

  If[[notA]or[notB]]then[not[AandB]] : {A B : Set} → ((¬ A) ⊎ (¬ B)) → ¬ (A × B)
  If[[notA]or[notB]]then[not[AandB]] (inj₁ a) A×B = a (proj₁ A×B)
  If[[notA]or[notB]]then[not[AandB]] (inj₂ b) A×B = b (proj₂ A×B)

-- Ex1.13
module Ex1-13 where
  open import Relation.Nullary
  open import Data.Sum

  not[not[Por[notP]]] : {P : Set} → ¬ (¬ (P ⊎ (¬ P)))
  not[not[Por[notP]]] ¬[P⊎[¬P]] = ¬[P⊎[¬P]] (inj₂ (λ p → ¬[P⊎[¬P]] (inj₁ p)))


-- Ex1.14
module Ex1-14 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  ind≡ : {A : Set} (C : (x y : A) (p : x ≡ y) → Set) → ((x : A) → C x x refl) → ((x y : A) (p : x ≡ y) → C x y p)
  ind≡ C c x .x refl = c x
{-
  f : {A : Set} (x : A) (p : x ≡ x) → p ≡ refl
  f x p = ind≡ (λ x y p → p ≡ refl) (λ y → refl) x x p
-}

-- Ex1.15
module Ex1-15 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  ind≡ : {A : Set} (C : (x y : A) (p : x ≡ y) → Set) → ((x : A) → C x x refl) → ((x y : A) (p : x ≡ y) → C x y p)
  ind≡ C c x .x refl = c x

  indis : {A : Set} (C : A → Set) →  (x y : A) → (p : x ≡ y) → C x → C y
  indis C = ind≡ (λ x y p → C x → C y) (λ x Cx → Cx)

-- Ex1.16
module Ex1-16 where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
  open import Data.Nat

  indℕ : ∀ {ℓ} → (C : ℕ → Set ℓ) → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
  indℕ C z f 0 = z
  indℕ C z f (suc n) = f n (indℕ C z f n)

  suc≡ : (i j : ℕ) → i + suc j ≡ suc (i + j)
  suc≡ = indℕ (λ i → (j : ℕ) → i + suc j ≡ suc (i + j))
              (λ j → refl)
              (λ i p j → cong suc (p j))

  commℕ : (i j : ℕ) → i + j ≡ j + i
  commℕ i j = indℕ ((λ n m → n + m ≡ m + n) i)
                   (indℕ (λ n → n + 0 ≡ n) refl (λ n p → cong suc p) i)
                   (λ n p → trans (suc≡ i n) (cong suc p)) j
