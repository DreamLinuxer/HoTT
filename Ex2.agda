module Ex2 where
open import Ch2-15 public

--Ex 2.1
module Ex2-1 where
  _▪₁_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _▪₁_ {ℓ} {A} {x} {y} {z} x≡y y≡z = ind≡ (λ x y x≡y → (z : A) → (y≡z : y ≡ z) → x ≡ z)
                                          (ind≡ (λ x z x≡z → x ≡ z) (λ x → refl x))
                                          x y x≡y z y≡z

  _▪₂_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _▪₂_ {ℓ} {A} {x} {.x} {z} (refl .x) y≡z = ind≡ (λ x z y≡z → x ≡ z) (λ x → refl x)
                                                 x z y≡z

  _▪₃_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _▪₃_ {ℓ} {A} {x} {y} {.y} x≡y (refl .y) = ind≡ (λ x y x≡y → x ≡ y) (λ x → refl x)
                                                 x y x≡y

  ▪₁≡₂ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
       → p ▪₁ q ≡ p ▪₂ q
  ▪₁≡₂ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₁ q ≡ p ▪₂ q)
                                      (λ x z q → ind≡ (λ x z q → (refl x ▪₁ q) ≡ (refl x ▪₂ q))
                                                      (λ x → refl (refl x))
                                                      x z q)
                                      x y p z q

  ▪₁≡₃ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
       → p ▪₁ q ≡ p ▪₃ q
  ▪₁≡₃ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₁ q ≡ p ▪₃ q)
                                      (λ x z q → ind≡ (λ x z q → (refl x ▪₁ q) ≡ (refl x ▪₃ q))
                                                      (λ x → refl (refl x))
                                                      x z q)
                                      x y p z q

  ▪₂≡₃ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
       → p ▪₂ q ≡ p ▪₃ q
  ▪₂≡₃ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₂ q ≡ p ▪₃ q)
                                      (λ x z q → ind≡ (λ x z q → (refl x ▪₂ q) ≡ (refl x ▪₃ q))
                                                      (λ x → refl (refl x))
                                                      x z q)
                                      x y p z q
