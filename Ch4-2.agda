{-# OPTIONS --without-K #-}
module Ch4-2 where
open import Base
open import Ch3-3
open import Ch3-11
open import Ex2
open import Ex3

-- Definition 4.2.1
ishae : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set _
ishae {A = A} {B} f = Σ[ g ∈ (B → A) ] Σ[ ε ∈ f ∘ g ~ id ] Σ[ η ∈ g ∘ f ~ id ] ((x : A) → ap f (η x) ≡ ε (f x))

-- Lemma 4.2.2
τ→v : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A)
    → (η : g ∘ f ~ id) (ε : f ∘ g ~ id)
    → ((x : A) → ap f (η x) ≡ ε (f x))
    → ((y : B) → ap g (ε y) ≡ η (g y))
τ→v f g η ε τ y = l-cancel _ _ (diag₁ ⁻¹ ▪ diag₂)
  where
  ηgfgy = η (g (f (g y)))
  gfgεy = ap (g ∘ f ∘ g) (ε y)

  diag₁ : ap g (ε y) ≡ ηgfgy ⁻¹  ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)
  diag₁ = ap g (ε y)
       ≡⟨ unit-left (ap g (ε y)) ⟩
          refl _ ▪ ap g (ε y)
       ≡⟨ ap (λ x → x ▪ ap g (ε y)) (p⁻¹▪p≡refly gfgεy ⁻¹) ⟩
          gfgεy ⁻¹ ▪ gfgεy ▪ ap g (ε y)
       ≡⟨ ap (λ x → x ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)) (ap∘ (f ∘ g) g _ _ (ε y) ⁻¹) ⟩
          ap g (ap (f ∘ g) (ε y)) ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)
       ≡⟨ ap (λ x → ap g x ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)) (comm~ _ ε _ ⁻¹) ⟩
          ap g (ε (f (g y))) ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)
       ≡⟨ ap (λ x → ap g x ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)) (τ (g y) ⁻¹) ⟩
          ap g (ap f (η (g y))) ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)
       ≡⟨ ap (λ x → x ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)) (ap∘ _ _ _ _ _) ⟩
          ap (g ∘ f) (η (g y)) ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)
       ≡⟨ ap (λ x → x ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y)) (comm~ (g ∘ f) η (g y) ⁻¹) ⟩
          ηgfgy ⁻¹  ▪ ap (g ∘ f ∘ g) (ε y) ▪ ap g (ε y) ∎

  diag₂ : ap g (ε y) ≡ ηgfgy ⁻¹ ▪ ap (g ∘ f ∘ g) (ε y) ▪ η (g y)
  diag₂ = ap g (ε y)
       ≡⟨ natural~' {f = g} η (ap g(ε y)) ⟩
          ηgfgy ⁻¹ ▪ ap (g ∘ f) (ap g (ε y)) ▪ η (g y)
       ≡⟨ ap (λ x → ηgfgy ⁻¹ ▪ x ▪ η (g y)) (ap∘ _ _ _ _ _) ⟩
          ηgfgy ⁻¹ ▪ ap (λ z → g (f (g z))) (ε y) ▪ η (g y) ∎

-- Theorem 4.2.3
qinv→ishae : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
           → qinv f → ishae f
qinv→ishae {A = A} {f = f} (g , ε , η) = g , ε' , η , τ
  where
  ε' : f ∘ g ~ id
  ε' b = ε (f (g b)) ⁻¹ ▪ ap f (η (g b)) ▪ ε b

  τ : (x : A) → ap f (η x) ≡ ε' (f x)
  τ a = ap f (η a)
     ≡⟨ natural~' {f = f} ε (ap f (η a)) ⟩
        ε (f (g (f a))) ⁻¹ ▪ ap (f ∘ g) (ap f (η a)) ▪ ε (f a)
     ≡⟨ ap (λ x → ε (f (g (f a))) ⁻¹ ▪ x ▪ ε (f a)) (ap∘ _ _ _ _ _) ⟩
        ε (f (g (f a))) ⁻¹ ▪ (ap (f ∘ g ∘ f) (η a)) ▪ ε (f a)
     ≡⟨ ap (λ x → ε (f (g (f a))) ⁻¹ ▪ x ▪ ε (f a)) (ap∘ _ _ _ _ _ ⁻¹) ⟩
        ε (f (g (f a))) ⁻¹ ▪ ap f (ap (g ∘ f) (η a)) ▪ ε (f a)
     ≡⟨ ap (λ x → ε (f (g (f a))) ⁻¹ ▪ ap f x ▪ ε (f a)) (comm~ _ η a ⁻¹) ⟩
        ε (f (g (f a))) ⁻¹ ▪ ap f (η (g (f a))) ▪ ε (f a) ∎

ishae→qinv : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
           → ishae f → qinv f
ishae→qinv (g , ε , η , τ) = g , ε , η

-- Definition 4.2.4
fib : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set _
fib {A = A} f y = Σ[ x ∈ A ] (f x ≡ y)

-- Lemma 4.2.5
[x,p≡x,p']≃Σ[fγ▪p'≡p] : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B)
                      → (f₁ f₂ : fib f y)
                      → (f₁ ≡ f₂) ≃ (Σ[ γ ∈ (pr₁ f₁ ≡ pr₁ f₂) ] (ap f γ ▪ pr₂ f₂ ≡ pr₂ f₁))
[x,p≡x,p']≃Σ[fγ▪p'≡p] f .(f x') (x , p) (x' , refl .(f x')) = 𝒇 , qinv→isequiv (𝒈 , α , β)
  where
  𝒇 : (x , p ≡ x' , refl (f x')) → (Σ[ γ ∈ (x ≡ x') ] (ap f γ ▪ refl (f x') ≡ p))
  𝒇 (refl .(_ , refl _)) = (refl x) , refl (refl (f x'))

  𝒈 : (Σ[ γ ∈ (x ≡ x') ] (ap f γ ▪ refl (f x') ≡ p)) → (x , p ≡ x' , refl (f x'))
  𝒈 (refl _ , refl .(refl _)) = refl _

  α : 𝒇 ∘ 𝒈 ~ id
  α (refl _ , refl .(refl _)) = refl _

  β : 𝒈 ∘ 𝒇 ~ id
  β (refl .(_ , refl _)) = refl _

-- Theorem 4.2.6
hae→isContr[fib] : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
                 → ishae f → (y : B) → isContr (fib f y)
hae→isContr[fib] {f = f} (g , ε , η , τ)  y = (g y , ε y) , h
  where
  h : (fib : fib f y) → g y , ε y ≡ fib
  h (x , p) = 𝒈 (ap g p ⁻¹ ▪ η x , φ)
    where
    𝒈 : Σ[ γ ∈ (g y ≡ x)] (ap f γ ▪ p ≡ ε y) → g y , ε y ≡ x , p
    𝒈 = pr₁ (pr₁ (pr₂ ([x,p≡x,p']≃Σ[fγ▪p'≡p] f y (g y , ε y) (x , p))))

    φ : ap f (ap g p ⁻¹ ▪ η x) ▪ p ≡ ε y
    φ = ap f (ap g p ⁻¹ ▪ η x) ▪ p ≡⟨ ap (λ x₁ → x₁ ▪ p) (ap▪ f _ _ _ _ _) ⟩
        ap f (ap g p ⁻¹) ▪ ap f (η x) ▪ p ≡⟨ ap (λ x₁ → ap f (ap g p ⁻¹) ▪ x₁ ▪ p) (τ x) ⟩
        ap f (ap g p ⁻¹) ▪ ε (f x) ▪ p ≡⟨ ap (λ x₁ → x₁ ▪ ε (f x) ▪ p) (ap⁻¹ f _ _ _) ⟩
        ap f (ap g p) ⁻¹ ▪ ε (f x) ▪ p ≡⟨ ap (λ x₁ → x₁ ⁻¹ ▪ ε (f x) ▪ p) (ap∘ _ _ _ _ _) ⟩
        ap (f ∘ g) p ⁻¹ ▪ ε (f x) ▪ p ≡⟨ natural~ {f = f} ε p ⁻¹ ⟩
        ε y ∎

-- Definition 4.2.7
linv : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set _
linv {A = A} {B} f = Σ[ g ∈ (B → A) ] ((g ∘ f) ~ id)

rinv : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set _
rinv {A = A} {B} f = Σ[ g ∈ (B → A) ] ((f ∘ g) ~ id)

-- Lemma 4.2.8
qinvf→qinv[f∘-] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
                → (f : A → B) → qinv f → qinv (_∘_ {A = C} f)
qinvf→qinv[f∘-] f (g , ε , η) = (_∘_ g) , (λ h → funext (λ x → ε (h x)))
                                        , (λ h → funext (λ x → η (h x)))

qinvf→qinv[-∘f] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
                → (f : A → B) → qinv f → qinv (λ h → _∘_ {C = C} h f)
qinvf→qinv[-∘f] f (g , ε , η) = (λ h → h ∘ g) , (λ h → funext (λ x → ap h (η x)))
                                              , (λ h → funext (λ x → ap h (ε x)))

-- Lemma 4.2.9
linv≃Σ[g∘f≡id] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
               → linv f ≃ (Σ[ g ∈ (B → A) ] (g ∘ f ≡ id))
linv≃Σ[g∘f≡id] {f = f} = (λ {(g , η) → g , (funext η)})
                       , qinv→isequiv ( (λ {(g , p) → g , (happly p)})
                                      , (λ {(g , p) → pairΣ≡ (refl g , uniqΠ≡ p)})
                                      , (λ {(g , η) → pairΣ≡ (refl g , compΠ≡ η)}))

rinv≃Σ[f∘g≡id] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B}
               → rinv f ≃ (Σ[ g ∈ (B → A) ] (f ∘ g ≡ id))
rinv≃Σ[f∘g≡id] {f = f} = (λ {(g , η) → g , (funext η)})
                       , qinv→isequiv ( (λ {(g , p) → g , (happly p)})
                                      , (λ {(g , p) → pairΣ≡ (refl g , uniqΠ≡ p)})
                                      , (λ {(g , η) → pairΣ≡ (refl g , compΠ≡ η)}))

qinv→isContr[linv] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
                   → (f : A → B) → qinv f → isContr (linv f)
qinv→isContr[linv] {A = A} {B} f qe = transport isContr (ua linv≃Σ[g∘f≡id] ⁻¹) isContr[Σ[g∘f≡id]]
  where
  isContr[Σ[g∘f≡id]] : isContr (Σ[ g ∈ (B → A) ] (g ∘ f ≡ id))
  isContr[Σ[g∘f≡id]] = hae→isContr[fib] (qinv→ishae (qinvf→qinv[-∘f] f qe)) id

qinv→isContr[rinv] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
                   → (f : A → B) → qinv f → isContr (rinv f)
qinv→isContr[rinv] {A = A} {B} f qe = transport isContr (ua (rinv≃Σ[f∘g≡id] {f = f}) ⁻¹) isContr[Σ[f∘g≡id]]
  where
  isContr[Σ[f∘g≡id]] : isContr (Σ[ g ∈ (B → A) ] (f ∘ g ≡ id))
  isContr[Σ[f∘g≡id]] = hae→isContr[fib] (qinv→ishae (qinvf→qinv[f∘-] f qe)) id

-- Definition 4.2.10
lcoh : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
     → linv f → Set _
lcoh {B = B} f (g , η) = Σ[ ε ∈ (f ∘ g ~ id) ] ((y : B) → ap g (ε y) ≡ η (g y))

rcoh : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
     → rinv f → Set _
rcoh {A = A} f (g , ε) = Σ[ η ∈ (g ∘ f ~ id) ] ((x : A) → ap f (η x) ≡ ε (f x))

-- Lemma 4.2.11
lcoh≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A) (η : g ∘ f ~ id) 
      → lcoh f (g , η) ≃ ((y : B) → _≡_ {A = fib g (g y)} (f (g y) , η (g y)) (y , refl (g y)))
lcoh≃ {A = A} {B} f g η = sym≃ (≃→Π≃ eq) ○ sym≃ (Π→ , Π→≃)
  where
  eq : (y : B) → (_≡_ {A = fib g (g y)} (f (g y) , η (g y)) (y , refl (g y)))
               ≃ (Σ[ γ ∈ (f (g y) ≡ y)] (ap g γ ≡ η (g y)))
  eq y = tran≃ ([x,p≡x,p']≃Σ[fγ▪p'≡p] g (g y) (f (g y) , η (g y)) (y , refl (g y)))
               (≃→Σ≃ (λ γ → idtoeqv (ap (λ x → x ≡ η (g y)) (unit-right _ ⁻¹))))

rcoh≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (g : B → A) (ε : f ∘ g ~ id) 
      → rcoh f (g , ε) ≃ ((x : A) → _≡_ {A = fib f (f x)} (g (f x) , ε (f x)) (x , refl (f x)))
rcoh≃ {A = A} {B} f g ε = sym≃ (≃→Π≃ eq) ○ sym≃ (Π→ , Π→≃)
  where
  eq : (x : A) → (_≡_ {A = fib f (f x)} (g (f x) , ε (f x)) (x , refl (f x)))
               ≃ (Σ[ γ ∈ (g (f x) ≡ x)] (ap f γ ≡ ε (f x)))
  eq x = tran≃ ([x,p≡x,p']≃Σ[fγ▪p'≡p] f (f x) (g (f x) , ε (f x)) (x , refl (f x)))
               (≃→Σ≃ (λ γ → idtoeqv (ap (λ x₁ → x₁ ≡ ε (f x)) (unit-right _ ⁻¹))))

-- Lemma 4.2.12
ishae→isContr[rcoh] : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
                    → ishae f → (ri : rinv f) → isContr (rcoh f ri)
ishae→isContr[rcoh] {A = A} f hae (g , ε) =
  transport isContr (ua (rcoh≃ f g ε) ⁻¹) (ΠisContr (λ a → AisProp→isContr[a≡a] (isProp[fib≡fib] a) _ _))
  where
  isProp[fib≡fib] : (a : A) → isProp (fib f (f a))
  isProp[fib≡fib] a = (pr₁ (isContra→isProp (hae→isContr[fib] hae (f a))))

-- Theorem 4.2.13
ishaeIsProp : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
            → isProp (ishae f)
ishaeIsProp {A = A} {B} f = transport id eq contr
  where
  open Ex3-5
  open Ex2-10
  eq : (ishae f → isContr (ishae f)) ≡ isProp (ishae f)
  eq = ua (isPropA≃[A→isContrA] {A = ishae f}) ⁻¹

  contr : ishae f → isContr (ishae f)
  contr hae = transport isContr (ua Σeq ⁻¹) (qinv→isContr[rinv] f (ishae→qinv hae))
    where
    Σeq : ishae f ≃ rinv f
    Σeq = assocΣ ▪≃ (isContrP→ΣPx≃A _ (rcoh f) (λ {(g , η) → ishae→isContr[rcoh] f hae (g , η)}))
