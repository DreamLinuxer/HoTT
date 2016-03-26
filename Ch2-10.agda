{-# OPTIONS --without-K #-}

module Ch2-10 where
open import Ch1 public
open import Ch2-9 public

--2.10
--Lemma 2.10.1
idtoeqv : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {ℓ} {A} {B} p = (p *) , ind≡ (λ A B p → isequiv (p *))
                                     (λ A → qinv→isequiv (id , (refl , refl)))
                                     A B p

--Axiom 2.10.3
postulate
  univalence : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → isequiv (idtoeqv {A = A} {B = B})

ua : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → (A ≃ B) → (A ≡ B)
ua {ℓ} {A} {B} with isequiv→qinv (univalence {A = A} {B = B})
ua | idtoeqv⁻¹ , (α , β) = idtoeqv⁻¹

elim≡ : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → pr₁ ∘ (idtoeqv {A = A} {B = B}) ≡ transport (λ x → x)
elim≡ {ℓ} {A} {B} = funext (λ p → refl (p *))

computation≡ : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} (f : A ≃ B) (x : A)→ transport (λ x → x) (ua f) x ≡ (pr₁ f) x
computation≡ {ℓ} {A} {B} f x with isequiv→qinv (univalence {A = A} {B = B})
computation≡ {A = A} {B = B} f x | idtoeqv⁻¹ , (α , β) = transport (λ x → x) (idtoeqv⁻¹ f) x
                                                       ≡⟨ refl ((idtoeqv⁻¹ f *) x) ⟩
                                                         (pr₁ (idtoeqv {A = A} {B = B} (idtoeqv⁻¹ f))) x
                                                       ≡⟨ ap (λ eq → (pr₁ eq) x) (α f) ⟩
                                                         pr₁ f x ∎

uniq≡ : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} (p : A ≡ B) → p ≡ ua (idtoeqv p)
uniq≡ {ℓ} {A} {B} p with isequiv→qinv (univalence {A = A} {B = B})
uniq≡ p | idtoeqv⁻¹ , (α , β) = (β p) ⁻¹

ref≡ : ∀ {ℓ} {A : Set ℓ} → refl A ≡ ua ref≃
ref≡ {ℓ} {A} with isequiv→qinv (univalence {A = A} {B = A})
ref≡ {ℓ} {A} | idtoeqv⁻¹ , (α , β) = refl A
                                   ≡⟨ β (refl A) ⁻¹ ⟩
                                     idtoeqv⁻¹ (idtoeqv (refl A))
                                   ≡⟨ ap idtoeqv⁻¹ (refl ref≃) ⟩
                                     (idtoeqv⁻¹ ref≃) ∎
