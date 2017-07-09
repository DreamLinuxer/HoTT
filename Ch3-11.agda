{-# OPTIONS --without-K #-}
module Ch3-11 where
open import Base
open import Ch3-1
open import Ch3-3
open import Ch3-6

-- Definition 3.11.1
isContr : ∀ {ℓ} (A : Set ℓ) → Set _
isContr A = Σ[ a ∈ A ] ((x : A) → a ≡ x)

-- Lemma 3.11.3
isContra→isProp : ∀ {ℓ} {A : Set ℓ} → isContr A → isProp A × A
isContra→isProp AisContr = (λ x y → (pr₂ AisContr x ⁻¹) ▪ (pr₂ AisContr y)) , pr₁ AisContr

isProp→isContra : ∀ {ℓ} {A : Set ℓ} → isProp A × A → isContr A
isProp→isContra (AisProp , a) = a , (λ x → AisProp a x)

isProp→≃1 : ∀ {ℓ} {A : Set ℓ} → isProp A × A → A ≃ 𝟙
isProp→≃1 = P≃𝟙

≃𝟙→isProp : ∀ {ℓ} {A : Set ℓ} → A ≃ 𝟙 → isProp A × A
≃𝟙→isProp (f , eq) with isequiv→qinv eq
≃𝟙→isProp (f , eq) | g , α , β = (λ x y → β x ⁻¹ ▪ ap g (uniq𝟙 (f x) ▪ uniq𝟙 (f y) ⁻¹) ▪ β y) , g ⋆

-- Lemma 3.11.4
isContrAisProp : ∀ {ℓ} {A : Set ℓ} → isProp (isContr A)
isContrAisProp (a , p) (a' , p') = pairΣ≡ (p a' , ΠisProp (λ x → PropisSet (pr₁ (isContra→isProp (a , p))) _ _) _ _)

-- Corollary 3.11.5
isContr→isContr[isContr] : ∀ {ℓ} {A : Set ℓ} → isContr A → isContr (isContr A)
isContr→isContr[isContr] c = c , isContrAisProp c

-- Lemma 3.11.6
ΠisContr : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} → ((a : A) → isContr (P a)) → isContr ((a : A) → P a)
ΠisContr PisContr = (λ a → pr₁ (PisContr a)) , ΠisProp (λ a → pr₁ (isContra→isProp (PisContr a))) _

retraction : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Set _
retraction {A = A} {B} r = Σ[ s ∈ (B → A) ] ((y : B) → r (s y) ≡ y)

is-retract : ∀ {ℓ ℓ'} (B : Set ℓ) (A : Set ℓ') → Set _
is-retract B A = Σ[ r ∈ (A → B) ] retraction r

-- Lemma 3.11.7
retract-prv-contra : ∀ {ℓ ℓ'} {B : Set ℓ} {A : Set ℓ'} → is-retract B A → isContr A → isContr B
retract-prv-contra (r , s , ε) (a₀ , contr) = r a₀ , (λ b → ap r (contr (s b)) ▪ ε b)

-- Lemma 3.11.8
Σ[a≡x]isContr : ∀ {ℓ} (A : Set ℓ) (a : A) → isContr (Σ[ x ∈ A ] a ≡ x)
Σ[a≡x]isContr A a = (a , refl a) , (λ {(x , p) → pairΣ≡ (p , transport[x↦a≡x] a p (refl a) ▪ unit-left p ⁻¹)})

-- Lemma 3.11.9
isContrP→ΣPx≃A : ∀ {ℓ ℓ'} (A : Set ℓ) (P : A → Set ℓ')
               → ((x : A) → isContr (P x)) → (Σ[ x ∈ A ] P x) ≃ A
isContrP→ΣPx≃A A P PisContr = pr₁ , qinv→isequiv (g , refl , β)
  where
  g : A → Σ A P
  g x = x , pr₁ (PisContr x)

  β : g ∘ pr₁ ~ id
  β (a , pa) = pairΣ≡ (refl a , pr₂ (PisContr a) pa)

isContrA→ΣPx≃Pa : ∀ {ℓ ℓ'} (A : Set ℓ) (P : A → Set ℓ')
                → (contr : isContr A) → (Σ[ x ∈ A ] P x) ≃ P (pr₁ contr)
isContrA→ΣPx≃Pa A P (a , p) = f , qinv→isequiv (g , {!!} , {!!})
  where
  f : Σ A P → P a
  f (a' , pa') = transport P (p a' ⁻¹) pa'

  g : P a → Σ A P
  g pa = a , pa

  α : f ∘ g ~ id
  α pa = ap (λ r → transport P r pa) (AisSet a a (p a ⁻¹) (refl a))
    where
    AisSet : isSet A
    AisSet = PropisSet (pr₁ (isContra→isProp (a , p)))

  β : g ∘ f ~ id
  β (a' , pa') = pairΣ≡ (p a' , q*[p*[u]]≡[[p▪q]*][u] P (p a' ⁻¹) (p a') pa' ▪ (ap (λ r → (r *) pa') (p⁻¹▪p≡refly (p a'))))

-- Lemma 3.11.10
AisProp→isContr[a≡a] : ∀ {ℓ} {A : Set ℓ} → isProp A → (x y : A) → isContr (x ≡ y)
AisProp→isContr[a≡a] AisProp x y = (AisProp x y) , (PropisSet AisProp x y _)

isContr[a≡a]→AisProp : ∀ {ℓ} {A : Set ℓ} → ((x y : A) → isContr (x ≡ y)) → isProp A
isContr[a≡a]→AisProp contr x y = pr₁ (contr x y)
