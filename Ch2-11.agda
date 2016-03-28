{-# OPTIONS --without-K #-}

module Ch2-11 where
open import Ch2-10 public

--2.11
--Theorem 2.11.1
ap≡ : ∀ {ℓ} {ℓ'} {ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} {a a' : A} →
      (f : A → B) → (isequiv f) → (isequiv (ap f {x = a} {y = a'}))
ap≡ {ℓ} {ℓ'} {ℓ''} {A} {B} {C} {a} {a'} f eqf with isequiv→qinv eqf
ap≡ {a = a} {a' = a'} f eqf | f⁻¹ , (α , β) =
    qinv→isequiv
    ( (λ p → β a ⁻¹ ▪ ap f⁻¹ p ▪ β a')
    , ( (λ q →  ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')
             ≡⟨ unit-right (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ⟩
                ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ refl (f a')
             ≡⟨ ap (λ p → ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ p) ((p⁻¹▪p≡refly (α (f a'))) ⁻¹) ⟩
                ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ (α (f a') ⁻¹ ▪ α (f a'))
             ≡⟨ assoc▪ (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) (α (f a') ⁻¹) (α (f a')) ⟩
                ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹ ▪ α (f a')
             ≡⟨ unit-left (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹ ▪ α (f a')) ⟩
                refl (f a) ▪ (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹ ▪ α (f a'))
             ≡⟨ ap (λ p → p ▪ (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹ ▪ α (f a'))) (p⁻¹▪p≡refly (α (f a)) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ α (f a) ▪ (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹ ▪ α (f a'))
             ≡⟨ (assoc▪ (α (f a) ⁻¹) (α (f a)) (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹ ▪ α (f a'))) ⁻¹ ⟩
                α (f a) ⁻¹ ▪ (α (f a) ▪ (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹ ▪ α (f a')))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ p) (assoc▪ (α (f a)) (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹) (α (f a'))) ⟩
                α (f a) ⁻¹ ▪ (α (f a) ▪ (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (p ▪ α (f a'))) (assoc▪ (α (f a)) (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) (α (f a') ⁻¹)) ⟩
                α (f a) ⁻¹ ▪ (α (f a) ▪ ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ⁻¹ ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (p ▪ α (f a') ⁻¹ ▪ α (f a')))
                   (ntran~ ((f ∘ f⁻¹) ∘ f) f (λ a → α (f a)) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ⟩
                α (f a) ⁻¹ ▪ (ap ((f ∘ f⁻¹) ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a') ▪ α (f a') ⁻¹ ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (p ▪ α (f a')))
                   (assoc▪ (ap ((f ∘ f⁻¹) ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) (α (f a')) (α (f a') ⁻¹) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap ((f ∘ f⁻¹) ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ (α (f a') ▪ α (f a') ⁻¹) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap ((f ∘ f⁻¹) ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ p ▪ α (f a')))
                   (p▪p⁻¹≡reflx (α (f a'))) ⟩
                α (f a) ⁻¹ ▪ (ap ((f ∘ f⁻¹) ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ refl (f (f⁻¹ (f a'))) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (p ▪ α (f a'))) ((unit-right (ap ((f ∘ f⁻¹) ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a'))) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap ((f ∘ f⁻¹) ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a') ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (p ▪ α (f a'))) ((ap∘ f (f ∘ f⁻¹) a a' (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap (f ∘ f⁻¹) (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (p ▪ α (f a'))) ((ap∘ f⁻¹ f (f a) (f a') (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a'))) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap f (ap f⁻¹ (ap f (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a'))) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f p ▪ α (f a'))) (ap∘ f f⁻¹ a a' (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ⟩
                α (f a) ⁻¹ ▪ (ap f (ap (f⁻¹ ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f p ▪ α (f a'))) (unit-left (ap (f⁻¹ ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a'))) ⟩
                α (f a) ⁻¹ ▪ (ap f (refl (f⁻¹ (f a)) ▪ (ap (f⁻¹ ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a'))) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f (p ▪ (ap (f⁻¹ ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a'))) ▪ α (f a'))) ((p▪p⁻¹≡reflx (β a)) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ β a ⁻¹ ▪ (ap (f⁻¹ ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a'))) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f p ▪ α (f a'))) ((assoc▪ (β a) (β a ⁻¹) (ap (f⁻¹ ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a'))) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ (β a ⁻¹ ▪ (ap (f⁻¹ ∘ f) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')))) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f (β a ▪ p) ▪ α (f a'))) (ntran~ id (f⁻¹ ∘ f) (λ a → β a ⁻¹) (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ ((ap id (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ▪ β a' ⁻¹)) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f (β a ▪ (p ▪ β a' ⁻¹)) ▪ α (f a'))) (apid a a' (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a')) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ (β a ⁻¹ ▪ ap f⁻¹ q ▪ β a' ▪ β a' ⁻¹)) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f (β a ▪ p) ▪ α (f a'))) ((assoc▪ (β a ⁻¹ ▪ ap f⁻¹ q) (β a') (β a' ⁻¹)) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ (β a ⁻¹ ▪ ap f⁻¹ q ▪ (β a' ▪ β a' ⁻¹))) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f (β a ▪ (β a ⁻¹ ▪ ap f⁻¹ q ▪ p)) ▪ α (f a'))) (p▪p⁻¹≡reflx (β a')) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ (β a ⁻¹ ▪ ap f⁻¹ q ▪ refl (f⁻¹ (f a')))) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f (β a ▪ p) ▪ α (f a'))) ((assoc▪ (β a ⁻¹) (ap f⁻¹ q) (refl (f⁻¹ (f a')))) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ (β a ⁻¹ ▪ (ap f⁻¹ q ▪ refl (f⁻¹ (f a'))))) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f (β a ▪ (β a ⁻¹ ▪ p)) ▪ α (f a'))) ((unit-right (ap f⁻¹ q)) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ (β a ⁻¹ ▪ ap f⁻¹ q)) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f p ▪ α (f a'))) (assoc▪ (β a) (β a ⁻¹) (ap f⁻¹ q)) ⟩
                α (f a) ⁻¹ ▪ (ap f (β a ▪ β a ⁻¹ ▪ ap f⁻¹ q) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f (p ▪ ap f⁻¹ q) ▪ α (f a'))) (p▪p⁻¹≡reflx (β a)) ⟩
                α (f a) ⁻¹ ▪ (ap f (refl (f⁻¹ (f a)) ▪ ap f⁻¹ q) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (ap f p ▪ α (f a'))) ((unit-left (ap f⁻¹ q)) ⁻¹) ⟩
                α (f a) ⁻¹ ▪ (ap f (ap f⁻¹ q) ▪ α (f a'))
             ≡⟨ ap (λ p → α (f a) ⁻¹ ▪ (p ▪ α (f a'))) (ap∘ f⁻¹ f (f a) (f a') q) ⟩
                α (f a) ⁻¹ ▪ (ap (f ∘ f⁻¹) q ▪ α (f a'))
             ≡⟨ assoc▪ (α (f a) ⁻¹) (ap (f ∘ f⁻¹) q) (α (f a')) ⟩
                α (f a) ⁻¹ ▪ ap (f ∘ f⁻¹) q ▪ α (f a')
             ≡⟨ ap (λ p → p ▪ α (f a')) (ntran~ id (f ∘ f⁻¹) (λ x → α x ⁻¹) q) ⟩
                ap id q ▪ α (f a') ⁻¹ ▪ α (f a')
             ≡⟨ ap (λ p → p ▪ α (f a') ⁻¹ ▪ α (f a')) (apid (f a) (f a') q) ⟩
                q ▪ α (f a') ⁻¹ ▪ α (f a')
             ≡⟨ (assoc▪ q (α (f a') ⁻¹) (α (f a'))) ⁻¹ ⟩
                q ▪ (α (f a') ⁻¹ ▪ α (f a'))
             ≡⟨ ap (λ p → q ▪ p) (p⁻¹▪p≡refly (α (f a'))) ⟩
                q ▪ refl (f a')
             ≡⟨ (unit-right q) ⁻¹ ⟩
                q ∎)
      , (λ p →  β a ⁻¹ ▪ ap f⁻¹ (ap f p) ▪ β a'
             ≡⟨ ap (λ q → β a ⁻¹ ▪ q ▪ β a') (ap∘ f f⁻¹ a a' p) ⟩
                β a ⁻¹ ▪ ap (f⁻¹ ∘ f) p ▪ β a'
             ≡⟨ ap (λ q → q ▪ β a') (ntran~ id (f⁻¹ ∘ f) (λ a → (β a) ⁻¹) p) ⟩
                ap id p ▪ β a' ⁻¹ ▪ β a'
             ≡⟨ (assoc▪ (ap id p) (β a' ⁻¹) (β a')) ⁻¹ ⟩
                ap id p ▪ (β a' ⁻¹ ▪ β a')
             ≡⟨ ap (λ q → ap id p ▪ q) (p⁻¹▪p≡refly (β a')) ⟩
                ap id p ▪ refl a'
             ≡⟨ (unit-right (ap id p)) ⁻¹ ⟩
                ap id p
             ≡⟨ apid a a' p ⟩
                p ∎)))
