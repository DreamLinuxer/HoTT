-- Formalization of https://arxiv.org/abs/1504.05531
-- Homotopy-initial algebras in type theory
{-# OPTIONS --without-K #-}
module hinitiality-4' where
open import Level
open import Base
open import Ch3
open import Ch4
open import Ex2

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} where
-- Definition 4.1
  Alg : ∀ {ℓ} → Set _
  Alg {ℓ} = Σ[ C ∈ Set ℓ ] ((x : A) → (B x → C) → C)

-- Definition 4.2
  isalghom : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} (f : pr₁ C → pr₁ D) → Set _
  isalghom {C = 𝑪} {𝑫} f = (x : A) (u : B x → C) → f (supc x u) ≡ supd x (f ∘ u)
    where
    C = pr₁ 𝑪
    supc = pr₂ 𝑪
    supd = pr₂ 𝑫

  Alghom : ∀ {ℓ ℓ'} (C : Alg {ℓ}) (D : Alg {ℓ'}) → Set _
  Alghom C D = Σ[ f ∈ (pr₁ C → pr₁ D) ] isalghom {C = C} {D} f

  idAlg : ∀ {ℓ} {C : Alg {ℓ}} → Alghom C C
  idAlg = id , (λ x u → refl _)

  _∘P_ : ∀ {ℓ ℓ' ℓ''} {C : Alg {ℓ}} {D : Alg {ℓ'}} {E : Alg {ℓ''}}
       → Alghom D E → Alghom C D → Alghom C E
  _∘P_ {E = 𝑬} 𝒈 𝒇 = (g ∘ f) , (λ x u → ap g (f' x u) ▪ g' x (f ∘ u))
    where
    f = pr₁ 𝒇
    g = pr₁ 𝒈
    f' = pr₂ 𝒇
    g' = pr₂ 𝒈

-- -- Definition 4.5
  FibAlg : ∀ {ℓ ℓ'} (C : Alg {ℓ}) → Set _
  FibAlg {ℓ' = ℓ'} 𝑪 = Σ[ E ∈ (C → Set ℓ') ] ((x : A) (u : B x → C) → ((y : B x) → E (u y)) → E (supc x u))
    where
    C = pr₁ 𝑪
    supc = pr₂ 𝑪

  assAlg : ∀ {ℓ ℓ'} {C : Alg {ℓ}} (E : FibAlg {ℓ' = ℓ'} C) → Alg
  assAlg {C = 𝑪} 𝑬 = (Σ[ z ∈ C ] (E z)) , (λ x u → supc x (pr₁ ∘ u) , e x (pr₁ ∘ u) (λ y → pr₂ (u y)))
    where
    C = pr₁ 𝑪
    supc = pr₂ 𝑪
    E = pr₁ 𝑬
    e = pr₂ 𝑬

  𝒆 : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {E : FibAlg {ℓ' = ℓ'} C} (f : (x : pr₁ C) → pr₁ E x)
    → (x : A) (u : B x → pr₁ C) → pr₁ E (pr₂ C x u)
  𝒆 {E = 𝑬} f x u = e x u (λ x → f (u x))
    where
    e = pr₂ 𝑬

  AlgSec : ∀ {ℓ ℓ'} (C : Alg {ℓ}) (E : FibAlg {ℓ' = ℓ'} C) → Set _
  AlgSec C E = Σ[ f ∈ ((x : pr₁ C) →  (pr₁ E x)) ] ((x : A) (u : B x → pr₁ C) → f (pr₂ C x u) ≡ 𝒆 {C = C} {E = E} f x u)

  𝒆~ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {E : FibAlg {ℓ' = ℓ'} C} {f g : (x : pr₁ C) → pr₁ E x}
     → (α : f ~ g) → (x : A) (u : B x → pr₁ C) → 𝒆 {C = C} {E = E} f x u ≡ 𝒆 {C = C} {E = E} g x u
  𝒆~ {E = E} {f} {g} α x u = ap (pr₂ E x u) (funext (λ x → α (u x)))

  AlgSec~ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {E : FibAlg {ℓ' = ℓ'} C}
          → (f g : AlgSec C E) → Set _
  AlgSec~ {C = 𝑪} {𝑬} 𝒇 𝒈 = Σ[ α ∈ (f ~ g) ] ((x : A) (u : B x → C) → f' x u ▪ ap (e x u) (funext (λ x → α (u x))) ≡ α (supc x u) ▪ g' x u)
    where
    C = pr₁ 𝑪
    E = pr₁ 𝑬
    supc = pr₂ 𝑪
    e = pr₂ 𝑬
    f = pr₁ 𝒇
    f' = pr₂ 𝒇
    g = pr₁ 𝒈
    g' = pr₂ 𝒈

  Alg~ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} (f g : Alghom C D) → Set _
  Alg~ {ℓ} {ℓ'} {𝑪} {𝑫} = AlgSec~ {C = 𝑪} {E = (λ _ → D) , (λ x u h → supd x h)}
    where
    D = pr₁ 𝑫
    supd = pr₂ 𝑫

  AlgSec≃ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {E : FibAlg {ℓ' = ℓ'} C} {f g : AlgSec C E}
          → f ≡ g ≃ AlgSec~ {C = C} {E = E} f g
  AlgSec≃ {C = 𝑪} {𝑬} {𝒇} {𝒈} = 𝒇 ≡ 𝒈
                             ≃⟨ Σ≃ ⟩
                                Σ[ p ∈ (f ≡ g) ] transport (λ h → (x : A) (u : B x → C) → h (supc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} h x u) p f' ≡ g'
                             ≃⟨ ≃→Σ≃ (λ p → idtoeqv (ap (λ r → r ≡ g') (eq₁ p f'))) ⟩
                                Σ[ p ∈ (f ≡ g) ] (λ x u → happly p (supc x u) ⁻¹ ▪ f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p) ≡ g'
                             ≃⟨ ≃→Σ≃ (λ p → (happly , funextentionality)) ⟩
                                Σ[ p ∈ (f ≡ g) ] ((x : A) →
                                     (λ u → happly p (supc x u) ⁻¹ ▪ f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p) ≡ g' x)
                             ≃⟨ ≃→Σ≃ (λ p → ≃→Π≃ (λ x → (happly , funextentionality))) ⟩
                                Σ[ p ∈ (f ≡ g) ] ((x : A) (u : B x → C) →
                                     (happly p (supc x u) ⁻¹ ▪ f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p) ≡ g' x u)
                             ≃⟨ ≃→Σ≃ (λ p → ≃→Π≃ (λ x → ≃→Π≃ (λ u →
                                          idtoeqv (ap (λ r → r ≡ g' x u) (assoc▪ _ _ _ ⁻¹) ▪ eq₂)))) ⟩
                                Σ[ p ∈ (f ≡ g) ] ((x : A) (u : B x → C) →
                                     (f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p) ≡ happly p (supc x u) ▪ g' x u)
                             ≃⟨ ≃→≃Σ (happly , funextentionality) (λ p → ≃→Π≃ (λ x → ≃→Π≃ (λ u → eq₃ p f' g' x u))) ⟩
                                AlgSec~ {C = 𝑪} {E = 𝑬} 𝒇 𝒈 ∎≃
    where
    C = pr₁ 𝑪
    supc = pr₂ 𝑪
    E = pr₁ 𝑬
    e = pr₂ 𝑬
    f = pr₁ 𝒇
    f' = pr₂ 𝒇
    g = pr₁ 𝒈
    g' = pr₂ 𝒈

    eq₁ : {f g : (x : C) → E x} (p : f ≡ g) (f' : (x : A) (u : B x → C) → f (supc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} f x u)
        → transport (λ h → (x : A) (u : B x → C) → h (supc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} h x u) p f'
        ≡ (λ x u → happly p (supc x u) ⁻¹ ▪ f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p)
    eq₁ (refl x) f' = funext (λ x → funext (λ u → unit-left _ ▪ unit-right _))

    eq₂ : ∀ {ℓ} {A : Set ℓ} {x y z : A} {p : y ≡ x} {q : y ≡ z} {r : x ≡ z}
        → (p ⁻¹ ▪ q ≡ r) ≡ (q ≡ p ▪ r)
    eq₂ {p = refl x} {refl .x} {r} = ap (λ s → refl x ≡ s) (unit-left _)

    eq₃ : {f g : (x : C) → E x} (p : f ≡ g)
        → (f' : (x : A) (u : B x → C) → f (supc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} f x u)
        → (g' : (x : A) (u : B x → C) → g (supc x u) ≡ 𝒆 {C = 𝑪} {E = 𝑬} g x u)
        → (x : A) (u : B x → C)
        → (f' x u ▪ ap (λ h → 𝒆 {C = 𝑪} {E = 𝑬} h x u) p ≡ happly p (supc x u) ▪ g' x u)
        ≃ f' x u ▪ ap (e x u) (funext (λ x → (happly p) (u x))) ≡ (happly p) (supc x u) ▪ g' x u
    eq₃ (refl f) f' g' x u = idtoeqv (ap (λ p → f' x u ▪ p ≡ refl (f (supc x u)) ▪ g' x u)
                                         (ap (ap (e x u)) (refΠ _)))

-- Lemma 4.4
  Alghom≃ : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} {f g : Alghom C D}
          → f ≡ g ≃ Alg~ {C = C} {D = D} f g
  Alghom≃ {C = 𝑪} {𝑫} = AlgSec≃ {C = 𝑪} {E = (λ _ → D) , (λ x u h → supd x h)}
    where
    D = pr₁ 𝑫
    supd = pr₂ 𝑫

-- Definition 4.9
  isalgequiv : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} (f  : Alghom C D) → Set _
  isalgequiv {C = C} {D} f = (Σ[ g ∈ (Alghom D C) ] (_∘P_ {C = C} {D = D} {E = C} g f) ≡ idAlg {C = C})
                           × (Σ[ h ∈ (Alghom D C) ] (_∘P_ {C = D} {D = C} {E = D} f h) ≡ idAlg {C = D})

  AlgEquiv : ∀ {ℓ ℓ'} {C : Alg {ℓ}} {D : Alg {ℓ'}} → Set _
  AlgEquiv {C = C} {D} = Σ[ f ∈ (Alghom C D) ] isalgequiv {C = C} {D = D} f
