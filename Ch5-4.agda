{-# OPTIONS --without-K #-}
module Ch5-4 where
open import Base
open import Level
open import Ch3
open import Ch4
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
ℕFib : ∀ {ℓ ℓ'} (A : ℕAlg {ℓ}) → Set _
ℕFib {ℓ' = ℓ'} A = Σ[ E ∈ (pr₁ A → Set ℓ') ] (E (pr₁ (pr₂ A)) × ((a : pr₁ A) → E a → E (pr₂ (pr₂ A) a)))

ℕSec : ∀ {ℓ ℓ'} (A : ℕAlg {ℓ}) (E : ℕFib {ℓ' = ℓ'} A) → Set (ℓ' ⊔ ℓ)
ℕSec (A , a₀ , aₛ) (E , e₀ , eₛ) = Σ[ f ∈ ((x : A) → E x) ] ((f a₀ ≡ e₀) × ((a : A) → f (aₛ a) ≡ eₛ a (f a)))

ℕSec~ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} {E : ℕFib {ℓ' = ℓ'} A} → (f g : ℕSec A E) → Set (ℓ' ⊔ ℓ)
ℕSec~ {A = (A , a₀ , aₛ)} {E = (E , e₀ , eₛ)} (f , f₀ , fₛ) (g , g₀ , gₛ)
      = Σ[ α ∈ (f ~ g) ] ((f₀ ≡ α a₀ ▪ g₀) × ((a : A) → fₛ a ▪ ap (eₛ a) (α a) ≡ α (aₛ a) ▪ gₛ a))

ℕSec≃ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} {E : ℕFib {ℓ' = ℓ'} A}
      → (f g : ℕSec A E) → (f ≡ g) ≃ (ℕSec~ f g)
ℕSec≃ {A = 𝑨@(A , a₀ , aₛ)} {E = 𝑬@(E , e₀ , eₛ)} 𝒇@(f , f₀ , fₛ) 𝒈@(g , g₀ , gₛ) =
      (f , f₀ , fₛ) ≡ (g , g₀ , gₛ)
   ≃⟨ Σ≃ ⟩
      Σ[ p ∈ (f ≡ g) ] (p *) (f₀ , fₛ) ≡ (g₀ , gₛ)
   ≃⟨ ≃→Σ≃ (λ p → (eq₁ p) ▪≃ (pair×≡⁻¹ , ×≃)) ⟩
      Σ[ p ∈ (f ≡ g) ] (((p *) f₀ ≡ g₀) × ((p *) fₛ ≡ gₛ))
   ≃⟨ ≃→Σ≃ (λ p → ≃→×≃ (idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = p})) (idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = p}))) ⟩
      Σ[ p ∈ (f ≡ g) ] ((f₀ ≡ (p ⁻¹ *) g₀) × (fₛ ≡ (p ⁻¹ *) gₛ))
   ≃⟨ ≃→Σ≃ (λ p → ≃→×≃ (eq₂ p _ _ _ _) ((happly , funextentionality) ▪≃ ≃→Π≃ (eq p))) ⟩
      Σ[ p ∈ (f ≡ g) ] ((f₀ ≡ (happly p) _ ▪ g₀) × ((a : A) → fₛ a ▪ ap (eₛ a) ((happly p) a) ≡ (happly p) (aₛ a) ▪ gₛ a))
   ≃⟨ ≃→≃Σ (happly , funextentionality) (λ p → ref≃) ⟩
      ℕSec~ 𝒇 𝒈 ∎≃
   where
   eq₁ : (p : f ≡ g) → ((p *) (f₀ , fₛ) ≡ g₀ , gₛ) ≃ (((p *) f₀ , (p *) fₛ) ≡ g₀ , gₛ)
   eq₁ (refl _) = idtoeqv (refl _)

   eq₂ : (p : f ≡ g) (a : A) (e : E a) (f' : f a ≡ e) (g' : g a ≡ e)
       → f' ≡ ((p ⁻¹) *) g' ≃ f' ≡ happly p a ▪ g'
   eq₂ (refl _) a _ (refl _) g' = idtoeqv (ap (λ q → refl (f a) ≡ q) (unit-left g'))

   eq : (p : f ≡ g) (x : A) → fₛ x ≡ transport (λ h → (a : A) → h (aₛ a) ≡ eₛ a (h a)) (p ⁻¹) gₛ x
                            ≃ fₛ x ▪ ap (eₛ x) (happly p x) ≡ happly p (aₛ x) ▪ gₛ x
   eq (refl _) a = idtoeqv ( ap (λ x → x ≡ gₛ a) (unit-right (fₛ a))
                           ▪ ap (λ x → fₛ a ▪ refl (eₛ a (f a)) ≡ x) (unit-left (gₛ a)))

isindℕ : ∀ {ℓ ℓ'} → (A : ℕAlg {ℓ}) → Set _
isindℕ {ℓ} {ℓ'} A = (E : ℕFib {ℓ' = ℓ'} A) → ℕSec A E

elimℕ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} (AisInd : isindℕ {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
      → (x : pr₁ A) (e₀ : E (pr₁ (pr₂ A))) (eₛ : ((a : pr₁ A) → E a → E (pr₂ (pr₂ A) a))) → E x
elimℕ {A = (A , a₀ , a₁)} AisInd E x e₀ eₛ = pr₁ (AisInd (E , e₀ , eₛ)) x

compℕ₀ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} (AisInd : isindℕ {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
       → (e₀ : E (pr₁ (pr₂ A))) (eₛ : ((a : pr₁ A) → E a → E (pr₂ (pr₂ A) a)))
       → elimℕ AisInd E (pr₁ (pr₂ A)) e₀ eₛ ≡ e₀
compℕ₀ {A = (A , a₀ , aₛ)} AisInd E e₀ eₛ = pr₁ (pr₂ (AisInd (E , e₀ , eₛ)))

compℕₛ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} (AisInd : isindℕ {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
       → (e₀ : E (pr₁ (pr₂ A))) (eₛ : ((a : pr₁ A) → E a → E (pr₂ (pr₂ A) a)))
       → (a : pr₁ A) → elimℕ AisInd E (pr₂ (pr₂ A) a) e₀ eₛ ≡ eₛ a (elimℕ AisInd E a e₀ eₛ)
compℕₛ {A = (A , a₀ , aₛ)} AisInd E e₀ eₛ = pr₂ (pr₂ (AisInd (E , e₀ , eₛ)))

ηℕ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} (AisInd : isindℕ {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
   → (e₀ : E (pr₁ (pr₂ A))) (eₛ : ((a : pr₁ A) → E a → E (pr₂ (pr₂ A) a)))
   → (f : (x : pr₁ A) → E x) → f (pr₁ (pr₂ A)) ≡ e₀
   → ((a : pr₁ A) → f (pr₂ (pr₂ A) a) ≡ eₛ a (f a))
   → (x : pr₁ A) → (f x) ≡ elimℕ AisInd E x e₀ eₛ
ηℕ {A = 𝑨@(A , a₀ , aₛ)} AisInd E e₀ eₛ f f₀ fₛ x = elimℕ AisInd F x F₀ Fₛ
  where
  F : A → Set _
  F x = f x ≡ elimℕ AisInd E x e₀ eₛ

  F₀ = f₀ ▪ compℕ₀ AisInd E e₀ eₛ ⁻¹
  Fₛ = (λ a fa → fₛ a ▪ ap (eₛ a) fa ▪ compℕₛ AisInd E e₀ eₛ a ⁻¹)

ηℕ₀ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} (AisInd : isindℕ {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
    → (e₀ : E (pr₁ (pr₂ A))) (eₛ : ((a : pr₁ A) → E a → E (pr₂ (pr₂ A) a)))
    → (f : (x : pr₁ A) → E x) → (f₀ : f (pr₁ (pr₂ A)) ≡ e₀)
    → (fₛ : (a : pr₁ A) → f (pr₂ (pr₂ A) a) ≡ eₛ a (f a))
    → ηℕ AisInd E e₀ eₛ f f₀ fₛ (pr₁ (pr₂ A)) ▪ compℕ₀ AisInd E e₀ eₛ ≡ f₀
ηℕ₀ {A = (A , a₀ , aₛ)} AisInd E e₀ eₛ f f₀ fₛ = ap (λ x → x ▪ compℕ₀ AisInd E e₀ eₛ) (compℕ₀ AisInd F F₀ Fₛ)
                                               ▪ assoc▪ _ _ _ ⁻¹
                                               ▪ ap (λ x → f₀ ▪ x) (p⁻¹▪p≡refly _)
                                               ▪ unit-right _ ⁻¹
  where
  F : A → Set _
  F x = f x ≡ elimℕ AisInd E x e₀ eₛ

  F₀ = f₀ ▪ compℕ₀ AisInd E e₀ eₛ ⁻¹
  Fₛ = (λ a fa → fₛ a ▪ ap (eₛ a) fa ▪ compℕₛ AisInd E e₀ eₛ a ⁻¹)

ηℕₛ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} (AisInd : isindℕ {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
    → (e₀ : E (pr₁ (pr₂ A))) (eₛ : ((a : pr₁ A) → E a → E (pr₂ (pr₂ A) a)))
    → (f : (x : pr₁ A) → E x) → (f₀ : f (pr₁ (pr₂ A)) ≡ e₀)
    → (fₛ : (a : pr₁ A) → f (pr₂ (pr₂ A) a) ≡ eₛ a (f a))
    → (a : pr₁ A)
    → ηℕ AisInd E e₀ eₛ f f₀ fₛ (pr₂ (pr₂ A) a)
    ▪ compℕₛ AisInd E e₀ eₛ a
    ▪ (ap (eₛ a) (ηℕ AisInd E e₀ eₛ f f₀ fₛ a)) ⁻¹ ≡ fₛ a
ηℕₛ {A = (A , a₀ , aₛ)} AisInd E e₀ eₛ f f₀ fₛ a =
    ηf (aₛ a) ▪ comₛ a ▪ ap (eₛ a) (ηf a) ⁻¹
 ≡⟨ ap (λ x → x ▪ comₛ a ▪ ap (eₛ a) (ηf a) ⁻¹) (compℕₛ AisInd F F₀ Fₛ a) ⟩
    fₛ a ▪ ap (eₛ a) (ηf a) ▪ comₛ a ⁻¹ ▪ comₛ a ▪ ap (eₛ a) (ηf a) ⁻¹
 ≡⟨ ap (λ x → x ▪ ap (eₛ a) (ηf a) ⁻¹) (assoc▪ _ _ _ ⁻¹ ▪ ap (λ x → fₛ a ▪ ap (eₛ a) (ηf a) ▪ x) (p⁻¹▪p≡refly _)) ⟩
    (fₛ a ▪ ap (eₛ a) (ηf a) ▪ refl _) ▪ ap (eₛ a) (ηf a) ⁻¹
 ≡⟨ assoc▪ _ _ _ ⁻¹ ⟩
    fₛ a ▪ ap (eₛ a) (ηf a) ▪ (refl _ ▪ ap (eₛ a) (ηf a) ⁻¹)
 ≡⟨ ap (λ x → fₛ a ▪ ap (eₛ a) (ηf a) ▪ x) (unit-left _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ⟩
    fₛ a ▪ (ap (eₛ a) (ηf a) ▪ ap (eₛ a) (ηf a) ⁻¹)
 ≡⟨ ap (λ x → fₛ a ▪ x) (p▪p⁻¹≡reflx _) ▪ unit-right _ ⁻¹ ⟩
    fₛ a ∎
  where
  ηf = ηℕ AisInd E e₀ eₛ f f₀ fₛ
  comₛ = compℕₛ AisInd E e₀ eₛ

  F : A → Set _
  F x = f x ≡ elimℕ AisInd E x e₀ eₛ

  F₀ = f₀ ▪ compℕ₀ AisInd E e₀ eₛ ⁻¹
  Fₛ = (λ a fa → fₛ a ▪ ap (eₛ a) fa ▪ compℕₛ AisInd E e₀ eₛ a ⁻¹)

isindℕ→isPropℕSec : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} (AisInd : isindℕ {ℓ' = ℓ'} A)
                   → (E : ℕFib {ℓ' = ℓ'} A)
                   → (f g : ℕSec A E) → f ≡ g
isindℕ→isPropℕSec {A = 𝑨@(A , a₀ , aₛ)} AisInd 𝑬@(E , e₀ , eₛ) 𝒇@(f , f₀ , fₛ) 𝒈@(g , g₀ , gₛ) =
  ≃← (ℕSec≃ {A = 𝑨} {E = 𝑬} 𝒇 𝒈) ((λ x → ηf x ▪ ηg x ⁻¹) , η₀ , ηₛ)
  where
  ηf = ηℕ AisInd E e₀ eₛ f f₀ fₛ
  ηg = ηℕ AisInd E e₀ eₛ g g₀ gₛ
  ηf₀ = ηℕ₀ AisInd E e₀ eₛ f f₀ fₛ
  ηfₛ = ηℕₛ AisInd E e₀ eₛ f f₀ fₛ
  ηg₀ = ηℕ₀ AisInd E e₀ eₛ g g₀ gₛ
  ηgₛ = ηℕₛ AisInd E e₀ eₛ g g₀ gₛ
  com₀ = compℕ₀ AisInd E e₀ eₛ
  comₛ = compℕₛ AisInd E e₀ eₛ
  η₀ = l-cancel {r = ηf a₀ ⁻¹} _ _
       (ηf a₀ ⁻¹ ▪ f₀
     ≡⟨ ap (λ x → ηf a₀ ⁻¹ ▪ x) (ηf₀ ⁻¹) ⟩
        ηf a₀ ⁻¹ ▪ (ηf a₀ ▪ com₀)
     ≡⟨ assoc▪ _ _ _ ▪ ap (λ x → x ▪ com₀) (p⁻¹▪p≡refly _) ⟩
        refl _ ▪ com₀
     ≡⟨ ap (λ x → x ▪ com₀) (p⁻¹▪p≡refly _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ▪ ap (λ x → ηg a₀ ⁻¹ ▪ x) ηg₀ ⟩
        ηg a₀ ⁻¹ ▪ g₀
     ≡⟨ unit-left (ηg a₀ ⁻¹ ▪ g₀) ▪ assoc▪ _ _ _ ▪ ap (λ x → x  ▪ ηg a₀ ⁻¹ ▪ g₀) (p⁻¹▪p≡refly _ ⁻¹) ⟩
        ηf a₀ ⁻¹ ▪ ηf a₀ ▪ ηg a₀ ⁻¹ ▪ g₀
     ≡⟨ ap (λ x → x ▪ g₀) (assoc▪ _ _ _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ⟩
        ηf a₀ ⁻¹ ▪ (ηf a₀ ▪ ηg a₀ ⁻¹ ▪ g₀) ∎)
  ηₛ = λ a → fₛ a ▪ ap (eₛ a) (ηf a ▪ ηg a ⁻¹)
          ≡⟨ ap (λ x → fₛ a ▪ x) (ap▪ _ _ _ _ _ _) ▪ assoc▪ _ _ _ ⟩
             fₛ a ▪ ap (eₛ a) (ηf a) ▪ ap (eₛ a) (ηg a ⁻¹)
          ≡⟨ ap (λ x → x ▪ ap (eₛ a) (ηf a) ▪ ap (eₛ a) (ηg a ⁻¹)) (ηfₛ a ⁻¹) ⟩
             ηf (aₛ a) ▪ comₛ a ▪ ap (eₛ a) (ηf a) ⁻¹ ▪ ap (eₛ a) (ηf a) ▪ ap (eₛ a) (ηg a ⁻¹)
          ≡⟨ assoc▪ _ _ _ ⁻¹ ▪ assoc▪ _ _ _ ⁻¹
           ▪ ap (λ x → ηf (aₛ a) ▪ comₛ a ▪ x)
                (assoc▪ _ _ _ ▪ ap (λ x → x ▪ ap (eₛ a) (ηg a ⁻¹)) (p⁻¹▪p≡refly _) ▪ unit-left _ ⁻¹) ⟩
             ηf (aₛ a) ▪ comₛ a ▪ ap (eₛ a) (ηg a ⁻¹)
          ≡⟨ assoc▪ _ _ _ ⁻¹ ▪ ap (λ x → ηf (aₛ a) ▪ x) ( unit-left _ ▪ assoc▪ _ _ _
                                                        ▪ ap (λ x → refl _ ▪ comₛ a ▪ x) (ap⁻¹ _ _ _ _)) ⟩
             ηf (aₛ a) ▪ (refl _ ▪ comₛ a ▪ ap (eₛ a) (ηg a) ⁻¹)
          ≡⟨ ap (λ x → ηf (aₛ a) ▪ (x ▪ comₛ a ▪ ap (eₛ a) (ηg a) ⁻¹)) (p⁻¹▪p≡refly _ ⁻¹) ⟩
             ηf (aₛ a) ▪ (ηg (aₛ a) ⁻¹ ▪ ηg (aₛ a) ▪ comₛ a ▪ ap (eₛ a) (ηg a) ⁻¹)
          ≡⟨ ap (λ x → ηf (aₛ a) ▪ x) (assoc▪ _ _ _ ⁻¹ ▪ assoc▪ _ _ _ ⁻¹ ▪ ap (λ x → ηg (aₛ a) ⁻¹ ▪ x) (assoc▪ _ _ _))
           ▪ assoc▪ _ _ _ ⟩
             ηf (aₛ a) ▪ ηg (aₛ a) ⁻¹ ▪ (ηg (aₛ a) ▪ comₛ a ▪ ap (eₛ a) (ηg a) ⁻¹)
          ≡⟨ ap (λ x → ηf (aₛ a) ▪ ηg (aₛ a) ⁻¹ ▪ x) (ηgₛ a) ⟩
             ηf (aₛ a) ▪ ηg (aₛ a) ⁻¹ ▪ gₛ a ∎

isindℕ→ishinitℕ : ∀ {ℓ ℓ'} {A : ℕAlg {ℓ}} → isindℕ {ℓ' = ℓ'} A → isHinitℕ {ℓ' = ℓ'} A
isindℕ→ishinitℕ {A = 𝑨@(A , a₀ , aₛ)} Aisind 𝑩@(B , b₀ , bₛ) = sec , isindℕ→isPropℕSec Aisind ((λ x → B) , b₀ , (λ a → bₛ)) sec
  where
  sec : ℕSec 𝑨 ((λ x → B) , b₀ , (λ a → bₛ))
  sec = Aisind ((λ x → B) , b₀ , (λ a → bₛ))

ℕisHinitℕ : ∀ {ℓ} → isHinitℕ {ℓ' = ℓ} (ℕ , 0 , succ)
ℕisHinitℕ = isindℕ→ishinitℕ {A = ℕA} ℕAisindℕ
  where
  ℕA : ℕAlg
  ℕA = (ℕ , 0 , succ)

  ℕAisindℕ : isindℕ ℕA
  ℕAisindℕ (E , e₀ , e₁) = indℕ E e₀ e₁ , refl e₀ , (λ a → refl (e₁ a (indℕ E e₀ e₁ a)))

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} where
  WAlg : ∀ {ℓ} → Set _
  WAlg {ℓ} = Σ[ C ∈ Set ℓ ] ((a : A) → (B a → C) → C)

  WHom : ∀ {ℓ ℓ'} (C : WAlg {ℓ}) (D : WAlg {ℓ'}) → Set _
  WHom 𝑪 𝑫 = Σ[ f ∈ (C → D) ] ((a : A) → (h : B a → C) → f (sc a h) ≡ sd a (f ∘ h))
    where
    C = pr₁ 𝑪
    sc = pr₂ 𝑪
    D = pr₁ 𝑫
    sd = pr₂ 𝑫

  isHinitW :  ∀ {ℓ ℓ'} (I : WAlg {ℓ}) → Set _
  isHinitW {ℓ' = ℓ'} I = (C : WAlg {ℓ = ℓ'}) → isContr (WHom I C)

-- Theorem 5.4.7
  FibWAlg : ∀ {ℓ ℓ'} (C : WAlg {ℓ}) → Set _
  FibWAlg {ℓ' = ℓ'} 𝑪 = Σ[ E ∈ (C → Set ℓ') ] ((x : A) (u : B x → C) → ((y : B x) → E (u y)) → E (sc x u))
    where
    C = pr₁ 𝑪
    sc = pr₂ 𝑪

  𝒆 : ∀ {ℓ ℓ'} {C : WAlg {ℓ}} {E : FibWAlg {ℓ' = ℓ'} C} (f : (x : pr₁ C) → pr₁ E x)
    → (x : A) (u : B x → pr₁ C) → pr₁ E (pr₂ C x u)
  𝒆 {E = 𝑬} f x u = e x u (λ x → f (u x))
    where
    e = pr₂ 𝑬

  WAlgSec : ∀ {ℓ ℓ'} (C : WAlg {ℓ}) (E : FibWAlg {ℓ' = ℓ'} C) → Set _
  WAlgSec 𝑪 𝑬 = Σ[ f ∈ ((x : C) →  (E x)) ] ((x : A) (u : B x → C) → f (sc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} f x u)
    where
    C = pr₁ 𝑪
    sc = pr₂ 𝑪
    E = pr₁ 𝑬
    e = pr₂ 𝑬

  𝒆~ : ∀ {ℓ ℓ'} {C : WAlg {ℓ}} {E : FibWAlg {ℓ' = ℓ'} C} {f g : (x : pr₁ C) → pr₁ E x}
     → (α : f ~ g) → (x : A) (u : B x → pr₁ C)
     → 𝒆 {C = C} {E = E} f x u ≡ 𝒆 {C = C} {E = E} g x u
  𝒆~ {E = E} {f} {g} α x u = ap (pr₂ E x u) (funext (λ x → α (u x)))

  WAlgSec~ : ∀ {ℓ ℓ'} {C : WAlg {ℓ}} {E : FibWAlg {ℓ' = ℓ'} C}
           → (f g : WAlgSec C E) → Set _
  WAlgSec~ {C = 𝑪} {𝑬} 𝒇 𝒈 = Σ[ α ∈ (f ~ g) ] ((x : A) (u : B x → C) →
                                                  f' x u ▪ 𝒆~ {C = 𝑪} {E = 𝑬} α x u ≡ α (sc x u) ▪ g' x u)
    where
    C = pr₁ 𝑪
    E = pr₁ 𝑬
    sc = pr₂ 𝑪
    e = pr₂ 𝑬
    f = pr₁ 𝒇
    f' = pr₂ 𝒇
    g = pr₁ 𝒈
    g' = pr₂ 𝒈

  AlgSec≃ : ∀ {ℓ ℓ'} {C : WAlg {ℓ}} {E : FibWAlg {ℓ' = ℓ'} C} {f g : WAlgSec C E}
          → f ≡ g ≃ WAlgSec~ {C = C} {E = E} f g
  AlgSec≃ {C = 𝑪} {𝑬} {𝒇} {𝒈} = 𝒇 ≡ 𝒈
                             ≃⟨ Σ≃ ⟩
                                Σ[ p ∈ (f ≡ g) ] transport (λ h → (x : A) (u : B x → C) → h (sc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} h x u) p f' ≡ g'
                             ≃⟨ ≃→Σ≃ (λ p → idtoeqv (ap (λ r → r ≡ g') (eq₁ p f'))) ⟩
                                Σ[ p ∈ (f ≡ g) ] (λ x u → happly p (sc x u) ⁻¹ ▪ f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p) ≡ g'
                             ≃⟨ ≃→Σ≃ (λ p → (happly , funextentionality)) ⟩
                                Σ[ p ∈ (f ≡ g) ] ((x : A) →
                                     (λ u → happly p (sc x u) ⁻¹ ▪ f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p) ≡ g' x)
                             ≃⟨ ≃→Σ≃ (λ p → ≃→Π≃ (λ x → (happly , funextentionality))) ⟩
                                Σ[ p ∈ (f ≡ g) ] ((x : A) (u : B x → C) →
                                     (happly p (sc x u) ⁻¹ ▪ f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p) ≡ g' x u)
                             ≃⟨ ≃→Σ≃ (λ p → ≃→Π≃ (λ x → ≃→Π≃ (λ u →
                                          idtoeqv (ap (λ r → r ≡ g' x u) (assoc▪ _ _ _ ⁻¹) ▪ eq₂)))) ⟩
                                Σ[ p ∈ (f ≡ g) ] ((x : A) (u : B x → C) →
                                     (f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p) ≡ happly p (sc x u) ▪ g' x u)
                             ≃⟨ ≃→≃Σ (happly , funextentionality) (λ p → ≃→Π≃ (λ x → ≃→Π≃ (λ u → eq₃ p f' g' x u))) ⟩
                                WAlgSec~ {C = 𝑪} {E = 𝑬} 𝒇 𝒈 ∎≃
    where
    C = pr₁ 𝑪
    sc = pr₂ 𝑪
    E = pr₁ 𝑬
    e = pr₂ 𝑬
    f = pr₁ 𝒇
    f' = pr₂ 𝒇
    g = pr₁ 𝒈
    g' = pr₂ 𝒈

    eq₁ : {f g : (x : C) → E x} (p : f ≡ g) (f' : (x : A) (u : B x → C) → f (sc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} f x u)
        → transport (λ h → (x : A) (u : B x → C) → h (sc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} h x u) p f'
        ≡ (λ x u → happly p (sc x u) ⁻¹ ▪ f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p)
    eq₁ (refl x) f' = funext (λ x → funext (λ u → unit-left _ ▪ unit-right _))

    eq₂ : ∀ {ℓ} {A : Set ℓ} {x y z : A} {p : y ≡ x} {q : y ≡ z} {r : x ≡ z}
        → (p ⁻¹ ▪ q ≡ r) ≡ (q ≡ p ▪ r)
    eq₂ {p = refl x} {refl .x} {r} = ap (λ s → refl x ≡ s) (unit-left _)

    eq₃ : {f g : (x : C) → E x} (p : f ≡ g)
        → (f' : (x : A) (u : B x → C) → f (sc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} f x u)
        → (g' : (x : A) (u : B x → C) → g (sc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} g x u)
        → (x : A) (u : B x → C)
        → (f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p ≡ happly p (sc x u) ▪ g' x u)
        ≃ f' x u ▪ ap (e x u) (funext (λ x → (happly p) (u x))) ≡ (happly p) (sc x u) ▪ g' x u
    eq₃ (refl f) f' g' x u = idtoeqv (ap (λ p → f' x u ▪ p ≡ refl (f (sc x u)) ▪ g' x u)
                                         (ap (ap (e x u)) (refΠ _)))

  isindW : ∀ {ℓ ℓ'} (C : WAlg {ℓ}) → Set _
  isindW {ℓ' = ℓ'} C = (E : FibWAlg {ℓ' = ℓ'} C) → WAlgSec C E

  module _ {ℓ ℓ'} {C : WAlg {ℓ}} {Cisind : isindW {ℓ' = ℓ'} C} where
    elim : (E : pr₁ C → Set ℓ')
         → (e : (x : A) (u : B x → pr₁ C) → ((y : B x) → E (u y)) → E (pr₂ C x u))
         → ((z : pr₁ C) → E z)
    elim E e = pr₁ (Cisind (E , e))

    comp : (E : pr₁ C → Set ℓ')
         → (e : (x : A) (u : B x → pr₁ C) → ((y : B x) → E (u y)) → E (pr₂ C x u))
         → (x : A) (u : B x → pr₁ C) → elim E e (pr₂ C x u) ≡ e x u (λ y → elim E e (u y))
    comp E e = (pr₂ (Cisind (E , e)))

    η : (E : pr₁ C → Set ℓ')
      → (e : (x : A) (u : B x → pr₁ C) → ((y : B x) → E (u y)) → E (pr₂ C x u))
      → (f : (z : pr₁ C) → E z)
      → (ϕ : (x : A) (u : B x → pr₁ C) → f (pr₂ C x u) ≡ e x u (λ y → f (u y)))
      → (z : pr₁ C) → f z ≡ elim E e z
    η E e f ϕ = elim T t
      where
      T : pr₁ C → Set _
      T z = f z ≡ elim E e z
      t = λ x u v → ϕ x u ▪ ap (e x u) (funext (λ y → v y)) ▪ comp E e x u ⁻¹

    η' : (E : pr₁ C → Set ℓ')
       → (e : (x : A) (u : B x → pr₁ C) → ((y : B x) → E (u y)) → E (pr₂ C x u))
       → (f : (z : pr₁ C) → E z)
       → (ϕ : (x : A) (u : B x → pr₁ C) → f (pr₂ C x u) ≡ e x u (λ y → f (u y)))
       → (x : A) (u : B x → pr₁ C) → η E e f ϕ (pr₂ C x u) ▪ comp E e x u ≡ ϕ x u ▪ ap (e x u) (funext (λ y → η E e f ϕ (u y)))
    η' E e f ϕ x u = η E e f ϕ (sc x u) ▪ comp E e x u
                  ≡⟨ ap (λ p → p ▪ comp E e x u) (comp T t x u) ▪ assoc▪ _ _ _ ⁻¹ ⟩
                     ϕ x u ▪ ap (e x u) (funext (λ y → η E e f ϕ (u y))) ▪ (comp E e x u ⁻¹ ▪ comp E e x u)
                 ≡⟨ ap (λ p → ϕ x u ▪ ap (e x u) (funext (λ y → η E e f ϕ (u y))) ▪ p) (p⁻¹▪p≡refly _)
                  ▪ unit-right _ ⁻¹ ⟩
                     ϕ x u ▪ ap (e x u) (funext (λ y → η E e f ϕ (u y))) ∎
      where
      sc = pr₂ C
      T : pr₁ C → Set _
      T z = f z ≡ elim E e z
      t = λ x u v → ϕ x u ▪ ap (e x u) (funext (λ y → v y)) ▪ comp E e x u ⁻¹

  isind→isPropAlgSec : ∀ {ℓ ℓ'} {C : WAlg {ℓ}} (CisInd : isindW {ℓ' = ℓ'} C)
                     → (E : FibWAlg {ℓ' = ℓ'} C)
                     → (f g : WAlgSec C E) → f ≡ g
  isind→isPropAlgSec {C = 𝑪@(C , sc)} CisInd 𝑬@(E , e) 𝒇@(f , f') 𝒈@(g , g') =
    ≃← (AlgSec≃ {C = 𝑪} {E = 𝑬}) ((λ x → ηf x ▪ ηg x ⁻¹) , α)
    where
    ηf = η {C = 𝑪} {Cisind = CisInd} E e f f'
    ηg = η {C = 𝑪} {Cisind = CisInd} E e g g'
    ηf' = η' {C = 𝑪} {Cisind = CisInd} E e f f'
    ηg' = η' {C = 𝑪} {Cisind = CisInd} E e g g'
    com = comp {C = 𝑪} {Cisind = CisInd} E e

    γ : ∀ {ℓ} {A : Set ℓ} {w x y z : A} {p : x ≡ y} {q : y ≡ z} {r : x ≡ w} {s : w ≡ z}
      → p ▪ q ≡ r ▪ s → p ▪ q ▪ s ⁻¹ ≡ r
    γ {p = refl x} {refl .x} {refl .x} {s} α = ap (λ q → q ▪ s ⁻¹) α ▪ assoc▪ _ _ _ ⁻¹
                                             ▪ ap (λ q → refl x ▪ q) (p▪p⁻¹≡reflx _)

    γ' : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ x₃ x₄ x₅ : A}
       → {p₁ : x₁ ≡ x₂} {p₂ : x₃ ≡ x₂} {p₃ : x₂ ≡ x₄} {p₄ : x₄ ≡ x₅}
       → p₁ ▪ p₂ ⁻¹ ▪ (p₂ ▪ p₃ ▪ p₄) ≡ p₁ ▪ p₃ ▪ p₄
    γ' {p₁ = refl x} {refl .x} {refl .x} {refl .x} = refl (refl x)

    γ'' : ∀ {ℓ} {A : Set ℓ} {w x y : A} {p p' : w ≡ x} {q q' : x ≡ y}
        → (α : p ≡ p') (β : q ≡ q') → p ▪ q ≡ p' ▪ q'
    γ'' (refl p) (refl q) = refl _

    γ''' : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ x₃ x₄ x₅ : A}
         → {p₁ : x₁ ≡ x₂} {p₂ : x₂ ≡ x₃} {p₃ : x₄ ≡ x₃} {p₄ : x₃ ≡ x₅}
         → (p₁ ▪ p₂ ▪ p₃ ⁻¹) ▪ (p₃ ▪ p₄) ≡ p₁ ▪ p₂ ▪ p₄
    γ''' {p₁ = refl x} {refl .x} {refl .x} {refl .x} = refl (refl x)

    ε : ∀ {f g h : (x : C) → E x} {ηf : f ≡ h} {ηg : g ≡ h}
      → (x : A) (u : B x → C)
      → (funext (λ y → happly ηf (u y) ▪ happly ηg (u y) ⁻¹))
      ≡ (funext (λ y → happly ηf (u y))) ▪ (funext (λ y → happly ηg (u y)) ⁻¹)
    ε {ηf = refl f} {refl .f} x u = unit-right _
                                  ▪ ap (λ p → funext (λ y → refl (f (u y))) ▪ p ⁻¹) (refΠ _)

    α : (x : A) (u : B x → C)
      → f' x u ▪ 𝒆~ {C = 𝑪} {E = 𝑬} (λ z → ηf z ▪ ηg z ⁻¹) x u
      ≡ ηf (sc x u) ▪ ηg (sc x u) ⁻¹ ▪ g' x u
    α x u = f' x u ▪ ap (e x u) (funext (λ x → ηf (u x) ▪ ηg (u x) ⁻¹))
         ≡⟨ γ'' (γ (ηf' x u) ⁻¹)
                ((ap (ap (e x u))
                     ( ap (λ α → funext (λ y → α (u y) ▪ ηg (u y) ⁻¹)) (compΠ≡ ηf ⁻¹)
                     ▪ ap (λ α → funext (λ y → (happly (funext ηf)) (u y) ▪ α (u y) ⁻¹)) (compΠ≡ ηg ⁻¹)
                     ▪ ε x u
                     ▪ ap (λ α → funext (λ y → (happly (funext ηf)) (u y)) ▪ (funext (λ y → α (u y)) ⁻¹)) (compΠ≡ ηg)
                     ▪ ap (λ α → funext (λ y → α (u y)) ▪ (funext (λ y → ηg (u y)) ⁻¹)) (compΠ≡ ηf)))
                ▪ ( ap▪ _ _ _ _ _ _
                  ▪ ap (λ p → ap (e x u) (funext (λ y → ηf (u y))) ▪ p) (ap⁻¹ _ _ _ _))) ⟩
            (ηf (sc x u) ▪ com x u ▪ ap (e x u) (funext (λ y → ηf (u y))) ⁻¹) ▪
            (ap (e x u) (funext (λ y → ηf (u y))) ▪ ap (e x u) (funext (λ y → ηg (u y))) ⁻¹)
         ≡⟨ γ''' ⟩
            ηf (sc x u) ▪ com x u ▪ ap (e x u) (funext (λ y → ηg (u y))) ⁻¹
         ≡⟨ γ' ⁻¹ ⟩
            ηf (sc x u) ▪ ηg (sc x u) ⁻¹ ▪
            (ηg (sc x u) ▪ com x u ▪ ap (e x u) (funext (λ y → ηg (u y))) ⁻¹)
         ≡⟨ ap (λ p → ηf (sc x u) ▪ ηg (sc x u) ⁻¹ ▪ p) (γ (ηg' x u)) ⟩
            ηf (sc x u) ▪ ηg (sc x u) ⁻¹ ▪ g' x u ∎

  isindW→isHinitW : ∀ {ℓ ℓ'} {C : WAlg {ℓ}} → isindW {ℓ' = ℓ'} C → isHinitW {ℓ' = ℓ'} C
  isindW→isHinitW {C = C} Cisind D =
    sec , isind→isPropAlgSec {C = C} Cisind fiber sec
    where
    fiber : FibWAlg C
    fiber = ((λ _ → pr₁ D) , (λ x u h → (pr₂ D) x h))

    sec : WAlgSec C fiber
    sec = Cisind fiber
  
  WisHinitW : ∀ {ℓ} → isHinitW {ℓ' = ℓ} (W A B , sup)
  WisHinitW = isindW→isHinitW {C = (W A B , sup)} Wisind
    where
    Wisind : isindW (W A B , sup)
    Wisind (E , e) = (indW E (λ a f → e a f)) , (λ x u → refl _)
