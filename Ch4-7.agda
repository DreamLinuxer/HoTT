{-# OPTIONS --without-K #-}
module Ch4-7 where
open import Base
open import Ch3-11
open import Ch4-2
open import Ch4-3
open import Ch4-4
open import Ex2

-- Theorem 4.7.1
isequiv[g∘f]×isequiv[g]→isequiv[f] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {g : B → A}
                                   → isequiv (g ∘ f) → isequiv g → isequiv f
isequiv[g∘f]×isequiv[g]→isequiv[f] {f = f} {g} eq[g∘f] eq[g] with isequiv→qinv eq[g∘f] | isequiv→qinv eq[g]
... | (g∘f⁻¹ , η' , ε') | (g⁻¹ , η , ε) = qinv→isequiv (g∘f⁻¹ ∘ g , h , ε')
    where
    h : f ∘ g∘f⁻¹ ∘ g ~ id
    h x = ε ((f ∘ g∘f⁻¹ ∘ g) x) ⁻¹
        ▪ ap g⁻¹ (η' (g x))
        ▪ ε x

isequiv[g∘f]×isequiv[f]→isequiv[g] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {g : B → A}
                                   → isequiv (g ∘ f) → isequiv f → isequiv g
isequiv[g∘f]×isequiv[f]→isequiv[g] {f = f} {g} eq[g∘f] eq[f] with isequiv→qinv eq[g∘f] | isequiv→qinv eq[f]
... | (g∘f⁻¹ , η' , ε') | (f⁻¹ , η , ε) = qinv→isequiv (f ∘ g∘f⁻¹ , η' , h)
    where
    h : (f ∘ g∘f⁻¹) ∘ g ~ id
    h x = ap ((f ∘ g∘f⁻¹) ∘ g) (η x) ⁻¹
        ▪ ap f (ε' (f⁻¹ x))
        ▪ η x

-- Definition 4.7.2
isRetract : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {X : Set ℓ₃} {Y : Set ℓ₄} (f : X → Y) (g : A → B) → Set _
isRetract {A = A} {B} {X} {Y} f g =
          Σ[ s ∈ (A → X) ] Σ[ r ∈ (X → A) ] Σ[ s' ∈ (B → Y) ] Σ[ r' ∈ (Y → B) ]
          Σ[ R ∈ (r ∘ s ~ id) ] Σ[ R' ∈ (r' ∘ s' ~ id) ]
          Σ[ L ∈ (f ∘ s ~ s' ∘ g) ] Σ[ K ∈ (g ∘ r ~ r' ∘ f) ]
          ((a : A) → ap g (R a) ▪ R' (g a) ⁻¹ ≡ K (s a) ▪ ap r' (L a))

-- Lemma 4.7.3
isRetract→isRetract[fib] : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {X : Set ℓ₃} {Y : Set ℓ₄}
                         → {f : X → Y} {g : A → B} → (ret : isRetract f g)
                         → ((b : B) → is-retract (fib f (pr₁ (pr₂ (pr₂ ret)) b)) (fib g b))
isRetract→isRetract[fib] {A = A} {f = f} {g} (s , r , s' , r' , R , R' , L , K , H) b = ψb , φb , ret
  where
  φb : fib g b → fib f (s' b)
  φb (a , p) = (s a) , (L a ▪ ap s' p)

  ψb : fib f (s' b) → fib g b
  ψb (x , q) = (r x) , (K x ▪ ap r' q ▪ R' b)

  Ha : (a : A) → ap g (R a) ⁻¹ ▪ (K (s a) ▪ ap r' (L a) ▪ R' (g a)) ≡ refl _
  Ha a = ap (λ x → ap g (R a) ⁻¹ ▪ (x ▪ R' (g a))) (H a ⁻¹)
       ▪ ap (λ x → ap g (R a) ⁻¹ ▪ x) (assoc▪ _ _ _ ⁻¹)
       ▪ assoc▪ _ _ _
       ▪ ap (λ x → ap g (R a) ⁻¹ ▪ ap g (R a) ▪ x) (p⁻¹▪p≡refly (R' (g a)))
       ▪ unit-right _ ⁻¹
       ▪ p⁻¹▪p≡refly (ap g (R a))

  ret : (y : fib g b) → ψb (φb y) ≡ y
  ret (a , refl _) = pairΣ≡ (R a , ap (λ x → (R a *) (K (s a) ▪ ap r' x ▪ R' (g a))) (unit-right _ ⁻¹)
                                 ▪ (transport[x↦fx≡gx] g (λ _ → g a) (R a) _
                                 ▪ (ap (λ x → x ▪ ap (λ _ → g a) (R a)) (Ha a)
                                 ▪ (unit-left _ ⁻¹
                                 ▪ apconst _))))
isRetract→isequiv : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {X : Set ℓ₃} {Y : Set ℓ₄}
                  → {f : X → Y} {g : A → B} → isequiv f → isRetract f g → isequiv g
isRetract→isequiv {f = f} {g} eqf ret =
                  (≃← (biinv≃ishae g) ∘ ≃→ (isContract≃ishae g))
                  (λ b → retract-prv-contra (isRetract→isRetract[fib] ret b)
                                            (((≃← (isContract≃ishae f) ∘ ≃→ (biinv≃ishae f)) eqf _)))

fibmap : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} (P : A → Set ℓ') (Q : A → Set ℓ'') → Set _
fibmap {A = A} P Q = (x : A) → P x → Q x

-- Definition 4.7.5
total : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : A → Set ℓ''}
      → (f : fibmap P Q) → Σ[ x ∈ A ] (P x) → Σ[ x ∈ A ] (Q x)
total f = λ w → (pr₁ w , f (pr₁ w) (pr₂ w))

-- Theorem 4.7.6
fibmap→fib[total]≃fib[f] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : A → Set ℓ''}
                         → (f : fibmap P Q) → (x : A) → (v : Q x)
                         → fib (total f) (x , v) ≃ fib (f x) v
fibmap→fib[total]≃fib[f] {A = A} {P} {Q} f x v =
                         Σ[ w ∈ (Σ[ a ∈ A ] (P a)) ] (total f) w ≡ (x , v)
                      ≃⟨ sym≃ Ex2-10.assocΣ ⟩
                         Σ[ a ∈ A ] Σ[ u ∈ (P a) ] (a , f a u) ≡ (x , v)
                      ≃⟨ Σ[≃]→≃ (λ a → Σ[≃]→≃ (λ u → Σ≃)) ⟩
                         Σ[ a ∈ A ] Σ[ u ∈ (P a) ] Σ[ p ∈ a ≡ x ] (p *) (f a u) ≡ v
                      ≃⟨ Σ[≃]→≃ (λ a → (λ {(u , p , α) → (p , u , α)})
                                     , (qinv→isequiv ( (λ {(p , u , α) → (u , p , α)})
                                                     , (λ {(p , u , α) → refl _})
                                                     , (λ {(u , p , α) → refl _})))) ⟩
                         Σ[ a ∈ A ] Σ[ p ∈ a ≡ x ] Σ[ u ∈ (P a) ] (p *) (f a u) ≡ v
                      ≃⟨ Ex2-10.assocΣ ⟩
                         Σ[ w ∈ (Σ[ a ∈ A ] (a ≡ x))  ] Σ[ u ∈ (P (pr₁ w)) ] ((pr₂ w) *) (f (pr₁ w) u) ≡ v
                      ≃⟨ isContrA→ΣPx≃Pa (Σ[ a ∈ A ] (a ≡ x)) _ (Σ[x≡a]isContr _ x) ⟩
                         fib (f x) v ∎≃

fibeq : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : A → Set ℓ''} (f : fibmap P Q) → Set _
fibeq {A = A} f = (x : A) → isequiv (f x)

-- Theorem 4.7.7
fibeq→isequv[total] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : A → Set ℓ''} {f : fibmap P Q}
                    → fibeq f → isequiv (total f)
fibeq→isequv[total] {f = f} eq = (≃→ (isContract≃isequiv (total f)))
                                 (λ {(x , v) → ≃isContr (≃← (isContract≃isequiv (f x)) (eq x) v)
                                                        (fibmap→fib[total]≃fib[f] f x v ⁻¹≃)})

isequv[total]→fibeq : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : A → Set ℓ''} {f : fibmap P Q}
                    → isequiv (total f) → fibeq f
isequv[total]→fibeq {f = f} eq x = ≃→ (isContract≃isequiv (f x))
                                      (λ u → ≃isContr (≃← (isContract≃isequiv (total f)) eq (x , u))
                                                      (fibmap→fib[total]≃fib[f] f x u))
