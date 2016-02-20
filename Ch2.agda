module Ch2 where

data _≡_ {A : Set} : (x y : A) → Set where
  refl : (x : A) → x ≡ x

infix 4 _≡_

ind≡ : {A : Set} (C : (x y : A) (p : x ≡ y) → Set) →
       ((x : A) → C x x (refl x)) →
       ((x y : A) (p : x ≡ y) → C x y p)
ind≡ C c x .x (refl .x) = c x

-- 2.1
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
p≡p▪reflx : {A : Set} {x y : A} (p : x ≡ y) → p ≡ p ▪ (refl y)
p≡p▪reflx {A} {x} {y} = ind≡ (λ x y p → p ≡ p ▪ refl y) (λ x → refl (refl x)) x y

p≡refly▪p : {A : Set} {x y : A} (p : x ≡ y) → p ≡ (refl x) ▪ p
p≡refly▪p {A} {x} {y} = ind≡ (λ x y p → p ≡ (refl x) ▪ p)
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

p▪[q▪r]≡[p▪q]▪r : {A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ▪ (q ▪ r) ≡ (p ▪ q) ▪ r
p▪[q▪r]≡[p▪q]▪r {A} {x} {y} {z} {w} p q r =
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

3-path : {A : Set} {x y : A} → {p q : x ≡ y} → {α γ : p ≡ q} → Set
3-path {A} {x} {y} {p} {q} {α} {γ} = α ≡ γ

