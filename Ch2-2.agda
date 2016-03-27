{-# OPTIONS --without-K #-}

module Ch2-2 where
open import Ch2-1 public

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
