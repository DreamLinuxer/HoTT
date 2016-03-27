{-# OPTIONS --without-K #-}

module Ch2-8 where
open import Ch2-7 public

--2.8
𝟙≡⁻¹ : {x y : 𝟙} → (x ≡ y) → 𝟙
𝟙≡⁻¹ = (λ _ → ⊤)

𝟙≡ : {x y : 𝟙} → 𝟙 → (x ≡ y)
𝟙≡ {x} {y} = (λ z → ind𝟙 (λ z → (x y : 𝟙) → x ≡ y)
                         (λ x y → ind𝟙 (λ x → (y : 𝟙) → x ≡ y)
                                       (λ y → ind𝟙 (λ y → ⊤ ≡ y) (refl ⊤) y)
                                       x y)
                         z x y)

--Theorem 2.8.1
𝟙≃ : {x y : 𝟙} → (x ≡ y) ≃ 𝟙
𝟙≃ {x} {y} = 𝟙≡⁻¹ , qinv→isequiv (𝟙≡ , ( (λ u → ind𝟙 (λ u → (𝟙≡⁻¹ {x = x} {y = y} ∘ 𝟙≡) u ≡ u)
                                                    (refl ⊤)
                                                    u)
                                      , (λ p → ind≡ (λ x y p → (𝟙≡ ∘ 𝟙≡⁻¹) p ≡ p)
                                                    (ind𝟙 (λ x → (𝟙≡ ∘ 𝟙≡⁻¹) (refl x) ≡ refl x)
                                                          (refl (refl ⊤)))
                                                    x y p)))
                                                     
uniq𝟙 : (u : 𝟙) → u ≡ ⊤
uniq𝟙 = ind𝟙 (λ u → u ≡ ⊤) (refl ⊤)
