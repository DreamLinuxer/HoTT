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
sym : {A : Set} (x y : A) → x ≡ y → y ≡ x
sym = ind≡ (λ x y x≡y → y ≡ x) (λ x → refl x)

--Lemma 2.1.2
trans : {A : Set} (x y z : A) → x ≡ y → y ≡ z → x ≡ z
trans {A = A} x y z x≡y y≡z = ind≡ (λ x y x≡y → (z : A) → (y≡z : y ≡ z) → x ≡ z)
                                   (ind≡ (λ x z x≡z → x ≡ z) (λ x → refl x))
                                   x y x≡y z y≡z
