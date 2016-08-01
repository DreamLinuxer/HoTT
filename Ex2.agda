{-# OPTIONS --without-K #-}
module Ex2 where

--Ex 2.1
module Ex2-1 where
  open import Ch2-1 public

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

  _▪₁≡₂_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
         → p ▪₁ q ≡ p ▪₂ q
  _▪₁≡₂_ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₁ q ≡ p ▪₂ q)
                                        (λ x z q → ind≡ (λ x z q → (refl x ▪₁ q) ≡ (refl x ▪₂ q))
                                                        (λ x → refl (refl x))
                                                        x z q)
                                        x y p z q

  _▪₁≡₃_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
         → p ▪₁ q ≡ p ▪₃ q
  _▪₁≡₃_ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₁ q ≡ p ▪₃ q)
                                        (λ x z q → ind≡ (λ x z q → (refl x ▪₁ q) ≡ (refl x ▪₃ q))
                                                        (λ x → refl (refl x))
                                                        x z q)
                                        x y p z q

  _▪₂≡₃_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
         → p ▪₂ q ≡ p ▪₃ q
  _▪₂≡₃_ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₂ q ≡ p ▪₃ q)
                                        (λ x z q → ind≡ (λ x z q → (refl x ▪₂ q) ≡ (refl x ▪₃ q))
                                                        (λ x → refl (refl x))
                                                        x z q)
                                        x y p z q

--Ex 2.2
module Ex2-2 where
  open Ex2-1
  _▪≡_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
       → (p ▪₁≡₂ q) ▪ (p ▪₂≡₃ q) ≡ p ▪₁≡₃ q
  _▪≡_ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z)
                                               → (p ▪₁≡₂ q) ▪ (p ▪₂≡₃ q) ≡ p ▪₁≡₃ q)
                                      (λ x z q → ind≡ (λ x z q → (refl x ▪₁≡₂ q) ▪ (refl x ▪₂≡₃ q) ≡ refl x ▪₁≡₃ q)
                                                      (λ x → refl (refl (refl x)))
                                                      x z q)
                                      x y p z q

--Ex 2.3
module Ex2-3 where
  open Ex2-1
  _▪₄_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _▪₄_ {ℓ} {A} {x} {y} {z} p q = ind≡' x (λ y p → (z : A) → y ≡ z → x ≡ z)
                                       (λ z q → q)
                                       y p z q

  _▪₁≡₄_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
         → p ▪₁ q ≡ p ▪₄ q
  _▪₁≡₄_ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₁ q ≡ p ▪₄ q)
                                        (λ x z q → ind≡ (λ x z q → (refl x ▪₁ q) ≡ (refl x ▪₄ q))
                                                        (λ x → refl (refl x))
                                                        x z q)
                                        x y p z q

  _▪₂≡₄_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
         → p ▪₂ q ≡ p ▪₄ q
  _▪₂≡₄_ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₂ q ≡ p ▪₄ q)
                                        (λ x z q → ind≡ (λ x z q → (refl x ▪₂ q) ≡ (refl x ▪₄ q))
                                                        (λ x → refl (refl x))
                                                        x z q)
                                        x y p z q

  _▪₃≡₄_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
         → p ▪₃ q ≡ p ▪₄ q
  _▪₃≡₄_ {ℓ} {A} {x} {y} {z} p q = ind≡ (λ x y p → (z : A) → (q : y ≡ z) → p ▪₃ q ≡ p ▪₄ q)
                                        (λ x z q → ind≡ (λ x z q → (refl x ▪₃ q) ≡ (refl x ▪₄ q))
                                                        (λ x → refl (refl x))
                                                        x z q)
                                        x y p z q

--Ex 2.4
module Ex2-4 where
  open import Level using (Lift)
  open import Ch1 public

  npath : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → Set ℓ
  npath {ℓ} {A} = recℕ (Set ℓ) A
                       (λ n np → Σ[ pr ∈ (np × np) ] (pr₁ pr ≡ pr₂ pr))

  boundary : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → Set ℓ
  boundary {ℓ} {A} = recℕ (Set ℓ) (Lift 𝟘)
                          (λ n b → npath {ℓ} {A} n × npath {ℓ} {A} n)
