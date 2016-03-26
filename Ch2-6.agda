{-# OPTIONS --without-K #-}

module Ch2-6 where
open import Ch1 public
open import Ch2-4 public

-- 2.6
pair×≡⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
           (x ≡ y) → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)
pair×≡⁻¹ p = (ap pr₁ p) , (ap pr₂ p)

pair×≡' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a a' : A} {b b' : B} →
          (a ≡ a') × (b ≡ b') → (a , b) ≡ (a' , b')
pair×≡' {ℓ} {ℓ'} {A} {B} {a} {a'} {b} {b'} =
       rec× ((a , b) ≡ (a' , b'))
            (λ p q → ind≡ (λ a a' p → a , b ≡ a' , b')
                          (ind≡ (λ b b' q → (x : A) → x , b ≡ x , b')
                                (λ b a → refl (a , b))
                                b b' q)
                          a a' p)

pair×≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
         (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y) → (x ≡ y)
pair×≡ {ℓ} {ℓ'} {A} {B} {a , b} {a' , b'} = pair×≡' {ℓ} {ℓ'} {A} {B} {a} {a'} {b} {b'}

--Theorem 2.6.2
×≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
     isequiv (pair×≡⁻¹ {ℓ} {ℓ'} {A} {B} {x} {y})
×≃ {ℓ} {ℓ'} {A} {B} {x} {y} =
   qinv→isequiv
   ( pair×≡
   , ((λ s → ind× (λ x → (y : A × B)
                       → (s : (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y))
                       → (pair×≡⁻¹ ∘ (pair×≡ {x = x} {y = y})) s ≡ s)
                  (λ a b y s →
                     ind× (λ y → (s : (a ≡ pr₁ y) × (b ≡ pr₂ y))
                               → (pair×≡⁻¹ ∘ (pair×≡ {x = (a , b)} {y = y})) s ≡ s)
                          (λ a' b' → ind× (λ s → (pair×≡⁻¹ ∘ pair×≡ {x = a , b} {y = a' , b'}) s ≡ s)
                                          (λ p q → ind≡ (λ a a' p → (pair×≡⁻¹ ∘ pair×≡') (p , q) ≡ p , q)
                                                        (λ a → ind≡ (λ b b' q → (pair×≡⁻¹ ∘ pair×≡') (refl a , q) ≡ refl a , q)
                                                                    (λ b → refl (refl a , refl b))
                                                                    b b' q)
                                                        a a' p))
                                          y s)
                          x y s)
   ,  (λ r → ind≡ (λ x y r → (pair×≡ ∘ pair×≡⁻¹) r ≡ r)
                  (λ x → ind× (λ x → (pair×≡ ∘ pair×≡⁻¹) (refl x) ≡ refl x)
                              (λ a b → refl (refl (a , b)))
                              x)
                  x y r)))

uniq×₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (z : A × B) → ((pr₁ z , pr₂ z) ≡ z)
uniq×₁ z = pair×≡ ((refl (pr₁ z)) , (refl (pr₂ z)))

--Theorem 2.6.4
transport× : ∀ {ℓ ℓ' ℓ''} {Z : Set ℓ} {A : Z → Set ℓ'} {B : Z → Set ℓ''}
             {z w : Z} (p : z ≡ w) (x : A z × B z) →
             transport (λ z → A z × B z) p x ≡ (transport (λ z → A z) p (pr₁ x) , transport (λ z → B z) p (pr₂ x))
transport× {ℓ} {ℓ'} {ℓ''} {Z} {A} {B} {z} {w} p x =
           ind≡ (λ z w p → (x : A z × B z) →
                           transport (λ z → A z × B z) p x ≡ transport (λ z → A z) p (pr₁ x) , transport (λ z → B z) p (pr₂ x))
                (λ z x → (uniq×₁ x) ⁻¹)
                z w p x

--Theorem 2.6.5
ap× : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {A' : Set ℓ₃} {B' : Set ℓ₄} →
      (g : A → A') (h : B → B') (x y : A × B) (p : pr₁ x ≡ pr₁ y) (q : pr₂ x ≡ pr₂ y) →
      (ap (λ x → (g (pr₁ x) , h (pr₂ x))) (pair×≡ {x = x} {y = y} (p , q))) ≡ (pair×≡ (ap g p , ap h q))
ap× {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {A} {B} {A'} {B'} g h (a , b) (a' , b') p q =
    ind≡ (λ a a' p → (q : b ≡ b') →
            ap (λ x → g (pr₁ x) , h (pr₂ x))
               (pair×≡ {x = (a , b)} {y = (a' , b')} (p , q))
            ≡
            pair×≡ (ap g p , ap h q))
         (λ a q → ind≡ (λ b b' q →
                          ap (λ x → g (pr₁ x) , h (pr₂ x))
                             (pair×≡ {x = (a , b)} {y = (a , b')} (refl a , q))
                          ≡
                          pair×≡ (ap g (refl a) , ap h q))
                       (λ b → refl (refl (g a , h b)))
                       b b' q)
         a a' p q
