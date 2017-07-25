{-# OPTIONS --without-K #-}
module Ch5-4 where
open import Base
open import Level
open import Ch3-11
open import Ch5-1
open import Ch5-3

-- Definition 5.4.1
ℕAlg : ∀ {ℓ} → Set _
ℕAlg {ℓ} = Σ[ C ∈ Set ℓ ] (C × (C → C))

-- Definition 5.4.2
ℕHom : ∀ {ℓ ℓ'} → ℕAlg {ℓ} → ℕAlg {ℓ'} → Set _
ℕHom C D = Σ[ h ∈ (pr₁ C → pr₁ D) ] ((h c₀ ≡ d₀) × ((c : pr₁ C) → h (cₛ c) ≡ dₛ (h c)))
  where
  c₀ = pr₁ (pr₂ C)
  cₛ = pr₂ (pr₂ C)
  d₀ = pr₁ (pr₂ D)
  dₛ = pr₂ (pr₂ D)

-- Definition 5.4.3
isHinitℕ : ∀ {ℓ ℓ'} → ℕAlg {ℓ} → Set _
isHinitℕ {ℓ} {ℓ'} I = (C : ℕAlg {ℓ'}) → isContr (ℕHom I C)

-- Theorem 5.4.4
_∘ℕ_ : ∀ {ℓ ℓ' ℓ''} {A : ℕAlg {ℓ}} {B : ℕAlg {ℓ'}} {C : ℕAlg {ℓ''}}
     → ℕHom B C → ℕHom A B → ℕHom A C
_∘ℕ_ {A = A , a₀ , aₛ} {B , b₀ , bₛ} {C , c₀ , cₛ} (g , g₀ , gₛ) (f , f₀ , fₛ) =
     g ∘ f , (ap g f₀ ▪ g₀) , (λ c → ap g (fₛ c) ▪ gₛ (f c))

idℕHom : ∀ {ℓ} {A : ℕAlg {ℓ}} → ℕHom A A
idℕHom {A = (A , a₀ , aₛ)} = id , refl a₀ , (λ c → refl (aₛ c))

pr₁∘ℕ≡ : ∀ {ℓ ℓ' ℓ''} {A : ℕAlg {ℓ}} {B : ℕAlg {ℓ'}} {C : ℕAlg {ℓ''}}
       → (g : ℕHom B C) → (f : ℕHom A B) → (pr₁ g) ∘ (pr₁ f) ≡ pr₁ (_∘ℕ_ {A = A} {B = B} {C = C} g f)
pr₁∘ℕ≡ {A = A , a₀ , aₛ} {B , b₀ , bₛ} {C , c₀ , cₛ} (g , _ , _) (f , _ , _) = refl _

initℕ≡ : ∀ {ℓ} → (I J : ℕAlg {ℓ})
       → isHinitℕ {ℓ' = ℓ} I → isHinitℕ {ℓ' = ℓ} J
       → I ≡ J
initℕ≡ {ℓ} I@(i , i₀ , iₛ) J@(j , j₀ , jₛ) IisHinitℕ JisHinitℕ =
  pairΣ≡ (ua i≃j , transport× (ua i≃j) (i₀ , iₛ) ▪ pair×≡ (i₀≡j₀ , iₛ≡jₛ))
  where
  f : ℕHom I J
  f = pr₁ (IisHinitℕ J)

  g : ℕHom J I
  g = pr₁ (JisHinitℕ I)

  f∘g≡id : pr₁ f ∘ pr₁ g ≡ id
  f∘g≡id = pr₁∘ℕ≡ {A = J} {B = I} {C = J} f g
         ▪ ap pr₁ (pr₂ (JisHinitℕ J) (_∘ℕ_ {A = J} {B = I} {C = J} f g) ⁻¹)
         ▪ ap pr₁ (pr₂ (JisHinitℕ J) (idℕHom {A = J}))

  g∘f≡id : pr₁ g ∘ pr₁ f ≡ id
  g∘f≡id = pr₁∘ℕ≡ {A = I} {B = J} {C = I} g f
         ▪ ap pr₁ (pr₂ (IisHinitℕ I) (_∘ℕ_ {A = I} {B = J} {C = I} g f) ⁻¹)
         ▪ ap pr₁ (pr₂ (IisHinitℕ I) (idℕHom {A = I}))


  i≃j : i ≃ j
  i≃j = pr₁ f , qinv→isequiv (pr₁ g , happly f∘g≡id , happly g∘f≡id)

  i₀≡j₀ : ((ua i≃j) *) i₀ ≡ j₀
  i₀≡j₀ = ((ua i≃j) *) i₀
       ≡⟨ computation≡ _ i₀ ⟩
          pr₁ f i₀
       ≡⟨ pr₁ (pr₂ f) ⟩
          j₀ ∎

  iₛ≡jₛ : ((ua i≃j) *) iₛ ≡ jₛ
  iₛ≡jₛ = transport→ (ua i≃j) _
        ▪ funext (λ x → ((ua i≃j) *) (iₛ (((ua i≃j ⁻¹) *) x))
                     ≡⟨ computation≡ _ _ ⟩
                        pr₁ f (iₛ (((ua i≃j ⁻¹) *) x))
                     ≡⟨ ap (λ p → pr₁ f (iₛ (transport id p x))) (≡⁻¹ _) ⟩
                        pr₁ f (iₛ (((ua (i≃j ⁻¹≃)) *) x))
                     ≡⟨ ap (pr₁ f ∘ iₛ) (computation≡ _ _) ⟩
                        pr₁ f (iₛ (pr₁ g x))
                     ≡⟨ ap (pr₁ f) (pr₂ (pr₂ g) x ⁻¹) ⟩
                        pr₁ f (pr₁ g (jₛ x))
                     ≡⟨ ≃ε i≃j (jₛ x) ⟩
                        jₛ x ∎)

-- Theorem 5.4.5
ℕisHinitℕ : ∀ {ℓ} → isHinitℕ {ℓ' = ℓ} (ℕ , 0 , succ)
ℕisHinitℕ (C , c₀ , cₛ) = (f , refl c₀ , (λ n → refl _)) , {!!}
  where
  f : ℕ → C
  f = recℕ C c₀ (λ n cn → cₛ cn)

  contr : (x : ℕHom (ℕ , 0 , succ) (C , c₀ , cₛ))
        → f ≡ pr₁ x
  contr (g , g₀ , gₛ) = uniq[ΠℕE] f g c₀ (λ n cn → cₛ cn) (refl c₀) g₀ (λ n → ap cₛ (refl _)) gₛ


WAlg : ∀ {ℓ ℓ' ℓ''} (A : Set ℓ) (B : A → Set ℓ') → Set _
WAlg {ℓ'' = ℓ''} A B = Σ[ C ∈ Set ℓ'' ] ((a : A) → (B a → C) → C)

WHom : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂)
     → (C : WAlg {ℓ'' = ℓ₃}A B) (D : WAlg {ℓ'' = ℓ₄} A B)
     → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
WHom A B (C , sc) (D , sd) = Σ[ f ∈ (C → D) ] ((a : A) → (h : B a → C) → f (sc a h) ≡ sd a (f ∘ h))

isHinitW :  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂) (I : WAlg {ℓ'' = ℓ₃} A B) → Set _
isHinitW {ℓ₄ = ℓ₄} A B I = (C : WAlg {ℓ'' = ℓ₄} A B) → isContr (WHom A B I C)

-- Theorem 5.4.7
WisHinitW : ∀ {ℓ₁ ℓ₂ ℓ₃} (A : Set ℓ₁) (B : A → Set ℓ₂)
          → isHinitW {ℓ₄ = ℓ₃} A B (W A B , sup)
WisHinitW A B (C , sc) = F , contr
  where
  F : WHom A B (W A B , sup) (C , sc)
  F = ((indW (λ _ → C) (λ a f h → sc a h)) , (λ a h → refl _))

  contr : (G : WHom A B (W A B , sup) (C , sc)) → F ≡ G
  contr (f , sf) = pairΣ≡ (e , funext (λ a → funext (λ h → {!!})))
        where
        e = (funext (indW (λ x → indW (λ _ → C) (λ a f₁ → sc a) x ≡ f x)
                                      (λ a h IH → ap (sc a) (funext (λ b → IH b)) ▪ sf a h ⁻¹)))
