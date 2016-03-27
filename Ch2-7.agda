{-# OPTIONS --without-K #-}

module Ch2-7 where
open import Ch2-6 public

--2.7
--Theorem 2.7.2
Σ≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
     (w ≡ w') ≃ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
Σ≃ {ℓ} {ℓ'} {A} {P} {w} {w'} =
    let f : {w w' : Σ[ x ∈ A ] P x} → (w ≡ w') → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
        f {w} {w'} = ind≡ (λ w w' p → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))))
                          (λ w → refl (pr₁ w) , refl (pr₂ w))
                          w w'
                          
        g : {w w' : Σ[ x ∈ A ] P x} → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))) → w ≡ w'
        g {w} {w'} = indΣ (λ w → (w' : Σ[ x ∈ A ] P x)
                               → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))) → w ≡ w')
                          (λ w₁ w₂ w' →
                             indΣ (λ w' → (Σ[ p ∈ (w₁ ≡ pr₁ w') ] ((_* {P = P} p) w₂ ≡ (pr₂ w'))) → (w₁ , w₂) ≡ w')
                                  (λ w₁' w₂' →
                                     indΣ (λ _ → w₁ , w₂ ≡ w₁' , w₂')
                                          (λ p q →
                                             ind≡ (λ w₁ w₁' p → (w₂ : P w₁) → (w₂' : P w₁')
                                                              → (p *) w₂ ≡ w₂' → (w₁ , w₂ ≡ w₁' , w₂'))
                                                  (λ w₁ w₂ w₂' q →
                                                     ind≡ (λ w₂ w₂' q → w₁ , w₂ ≡ w₁ , w₂')
                                                          (λ w₂ → refl (w₁ , w₂))
                                                          w₂ w₂' q)
                                                  w₁ w₁' p w₂ w₂' q))
                                  w')
                          w w'
                          
        f∘g~id : {w w' : Σ[ x ∈ A ] P x} → (f {w} {w'}) ∘ g ~ id
        f∘g~id {w} {w'} r = indΣ (λ w → (w' : Σ[ x ∈ A ] P x)
                                      → (r : Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
                                      → f {w} {w'} (g r) ≡ r)
                                 (λ w₁ w₂ w' r →
                                    indΣ (λ w' → (r : Σ[ p ∈ (w₁ ≡ pr₁ w') ] ((_* {P = P} p) w₂ ≡ (pr₂ w')))
                                               → f {w₁ , w₂} {w'} (g r) ≡ r)
                                         (λ w₁' w₂' r →
                                            indΣ (λ r → f {w₁ , w₂} {w₁' , w₂'} (g r) ≡ r)
                                                 (λ p q →
                                                    ind≡ (λ w₁ w₁' p → (w₂ : P w₁) → (w₂' : P w₁')
                                                                     → (q : (p *) w₂ ≡ w₂')
                                                                     → f {w₁ , w₂} {w₁' , w₂'} (g (p , q)) ≡ (p , q))
                                                         (λ w₁ w₂ w₂' q →
                                                            ind≡ (λ w₂ w₂' q → f {w₁ , w₂} {w₁ , w₂'} (g (refl w₁ , q)) ≡ (refl w₁ , q))
                                                                 (λ w₂ → refl (refl w₁ , refl w₂))
                                                                 w₂ w₂' q)
                                                         w₁ w₁' p w₂ w₂' q)
                                                 r)
                                         w' r)
                                 w w' r
                                 
        g∘f~id : {w w' : Σ[ x ∈ A ] P x} → (g {w} {w'}) ∘ f ~ id
        g∘f~id {w} {w'} p = ind≡ (λ w w' p → g {w} {w'} (f p) ≡ p)
                                 (indΣ (λ w → g (f (refl w)) ≡ refl w)
                                       (λ w₁ w₂ → refl (refl (w₁ , w₂))))
                                 w w' p
    in  f , qinv→isequiv (g , (f∘g~id {w} {w'} , g∘f~id))

--Corollary 2.7.3
uniqΣ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} → (z : Σ[ x ∈ A ] P x) → z ≡ (pr₁ z , pr₂ z)
uniqΣ {ℓ} {ℓ'} {A} {P} z with Σ≃ {w = z} {w' = (pr₁ z , pr₂ z)}
uniqΣ z | f , ((g , α) , (h , β)) = g (refl (pr₁ z) , refl (pr₂ z))

pairΣ≡⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
           (w ≡ w') → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
pairΣ≡⁻¹ {w = w} {w' = w'} with Σ≃ {w = w} {w' = w'}
pairΣ≡⁻¹ | f , ((g , α) , (h , β)) = f

pairΣ≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
         (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))) → w ≡ w'
pairΣ≡ {w = w} {w' = w'} with Σ≃ {w = w} {w' = w'}
pairΣ≡ | f , ((g , α) , (h , β)) = g

--Theorem 2.7.4
liftΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : (Σ[ x ∈ A ] (P x)) → Set ℓ''} →
        {x y : A} (p : x ≡ y) (u : P x) (z : Q (x , u)) →
        _* {P = λ x → Σ[ u ∈ (P x) ] (Q (x , u))} p (u , z)
        ≡
        ((p *) u , _* {P = Q} (pairΣ≡ (p , refl ((p *) u))) z)
liftΣ {ℓ} {ℓ'} {ℓ''} {A} {P} {Q} {x} {y} p u z =
      ind≡ (λ x y p → (u : P x) → (z : Q (x , u))
                    → _* {P = λ x → Σ[ u ∈ (P x) ] (Q (x , u))} p (u , z)
                    ≡ ((p *) u , _* {P = Q} (pairΣ≡ (p , refl ((p *) u))) z))
           (λ x u z → refl (u , z))
           x y p u z
