{-# OPTIONS --without-K #-}

module Ch2-15 where
open import Ch2-14 public

--2.15.1
×→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : Set ℓ'} {B : Set ℓ''}
   → (X → A × B) → (X → A) × (X → B)
×→ f = (pr₁ ∘ f) , (pr₂ ∘ f)

--Theorem 2.15.2
×→≃ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : Set ℓ'} {B : Set ℓ''}
    → isequiv (×→ {X = X} {A = A} {B = B})
×→≃ = qinv→isequiv ( (λ {(g , h) → λ x → (g x , h x)})
                   , ( (λ {(g , h) →  (λ x → g x) , (λ x → h x)
                                   ≡⟨ pair×≡ (refl g , refl h) ⟩
                                      (g , h) ∎})
                     , (λ f →  (λ x → ((pr₁ ∘ f) x , (pr₂ ∘ f) x))
                            ≡⟨ funext (λ x → pair×≡ ((refl (pr₁ (f x))) , (refl (pr₂ (f x))))) ⟩
                               f ∎)))

--2.15.4
Π×→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''}
    → ((x : X) → (A x × B x)) → ((x : X) → A x) × ((x : X) → B x)
Π×→ f = (λ x → pr₁ (f x)) , (λ x → pr₂ (f x))

--Theorem 2.15.5
Π×→≃ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''}
     → isequiv (Π×→ {X = X} {A = A} {B = B})
Π×→≃ = qinv→isequiv ( (λ {(g , h) → λ x → (g x , h x)})
                    , ( (λ {(g , h) → (λ x → g x) , (λ x → h x)
                                   ≡⟨ pair×≡ (refl g , refl h) ⟩
                                      (g , h) ∎})
                      , ((λ f → (λ x → (pr₁ (f x) , pr₂ (f x)))
                             ≡⟨ funext (λ x → pair×≡ ((refl (pr₁ (f x))) , (refl (pr₂ (f x))))) ⟩
                                f ∎))))

--2.15.6
Π→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {P : (x : X) → A x → Set ℓ''}
   → ((x : X) → Σ[ a ∈ (A x) ] P x a)
   → Σ[ g ∈ ((x : X) → A x) ] ((x : X) → P x (g x))
Π→ f = (λ x → pr₁ (f x)) , (λ x → pr₂ (f x))

--Theorem 2.15.7
Π→≃ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {P : (x : X) → A x → Set ℓ''}
    → isequiv (Π→ {X = X} {A = A} {P = P})
Π→≃ = qinv→isequiv ( (λ {(g , h) → λ x → (g x , h x)})
                   , ( (λ {(g , h) → (λ x → g x) , (λ x → h x)
                                  ≡⟨ pairΣ≡ (refl g , refl h) ⟩
                                     (g , h) ∎})
                     , (λ f → (λ x → (pr₁ (f x) , pr₂ (f x)))
                           ≡⟨ funext (λ x → pairΣ≡ ((refl (pr₁ (f x))) , ((refl (pr₂ (f x)))))) ⟩
                              f ∎)))

×→Π : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : A × B → Set ℓ''}
    → ((w : A × B) → C w)
    → ((x : A) → (y : B) → C (x , y))
×→Π f = λ x y → f (x , y)

Π→× : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : A × B → Set ℓ''}
    → ((x : A) → (y : B) → C (x , y))
    → ((w : A × B) → C w)
Π→× {C = C} f = ind× C f

×→Π≃ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : A × B → Set ℓ''}
     → isequiv (×→Π {A = A} {B = B} {C = C})
×→Π≃ = qinv→isequiv (Π→× , ( (λ f → refl f)
                           , (λ f → funext (λ {(a , b) → refl (f (a , b))}))))

Σ→Π : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : Σ[ x ∈ A ] B x → Set ℓ''}
    → ((w : Σ[ x ∈ A ] B x) → C w)
    → ((x : A) → (y : B x) → C (x , y))
Σ→Π f = λ x y → f (x , y)

Π→Σ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : Σ[ x ∈ A ] B x → Set ℓ''}
    → ((x : A) → (y : B x) → C (x , y))
    → ((w : Σ[ x ∈ A ] B x) → C w)
Π→Σ {C = C} f = indΣ C f

Σ→Π≃ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : Σ[ x ∈ A ] B x → Set ℓ''}
     → isequiv (Σ→Π {A = A} {B = B} {C = C})
Σ→Π≃ = qinv→isequiv (Π→Σ , ( (λ f → refl f)
                           , (λ f → funext (λ {(a , b) → refl (f (a , b))}))))

pathind≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {a : A} {B : (x : A) (p : a ≡ x) → Set ℓ'}
         → isequiv (ind≡' {A = A} a B)
pathind≃ {a = a} {B = B} = qinv→isequiv ( (λ f → f a (refl a))
                                        , ( (λ g → funext (λ x → funext (λ p →
                                                     ind≡' a (λ x p → ind≡' a B (g a (refl a)) x p ≡ g x p)
                                                             (refl (g a (refl a))) x p)))
                                          , (λ h → refl h)))
