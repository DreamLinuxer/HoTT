{-# OPTIONS --without-K #-}

module Ch2-10 where
open import Ch2-9 public

--2.10
--Lemma 2.10.1
idtoeqv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {ℓ} {A} {B} p = (p *) , ind≡ (λ A B p → isequiv (p *))
                                     (λ A → qinv→isequiv (id , (refl , refl)))
                                     A B p

--Axiom 2.10.3
postulate
  univalence : ∀ {ℓ} {A B : Set ℓ} → isequiv (idtoeqv {A = A} {B = B})

ua : ∀ {ℓ} {A B : Set ℓ} → (A ≃ B) → (A ≡ B)
ua {ℓ} {A} {B} with isequiv→qinv (univalence {A = A} {B = B})
ua | idtoeqv⁻¹ , (α , β) = idtoeqv⁻¹

elim≡ : ∀ {ℓ} {A B : Set ℓ} → pr₁ ∘ (idtoeqv {A = A} {B = B}) ≡ transport (λ x → x)
elim≡ {ℓ} {A} {B} = funext (λ p → refl (p *))

computation≡ : ∀ {ℓ} {A B : Set ℓ} (f : A ≃ B) (x : A) → transport (λ x → x) (ua f) x ≡ (pr₁ f) x
computation≡ {ℓ} {A} {B} f x with isequiv→qinv (univalence {A = A} {B = B})
computation≡ {A = A} {B = B} f x | idtoeqv⁻¹ , (α , β) = transport (λ x → x) (idtoeqv⁻¹ f) x
                                                       ≡⟨ refl ((idtoeqv⁻¹ f *) x) ⟩
                                                         (pr₁ (idtoeqv {A = A} {B = B} (idtoeqv⁻¹ f))) x
                                                       ≡⟨ ap (λ eq → (pr₁ eq) x) (α f) ⟩
                                                         pr₁ f x ∎

uniq≡ : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) → p ≡ ua (idtoeqv p)
uniq≡ {ℓ} {A} {B} p with isequiv→qinv (univalence {A = A} {B = B})
uniq≡ p | idtoeqv⁻¹ , (α , β) = (β p) ⁻¹

comp≡ : ∀ {ℓ} {A B : Set ℓ} (eq : A ≃ B) → eq ≡ idtoeqv (ua eq)
comp≡ {ℓ} {A} {B} eq with isequiv→qinv (univalence {A = A} {B = B})
comp≡ eq | idtoeqv⁻¹ , (α , β) = (α eq) ⁻¹

ref≡ : ∀ {ℓ} {A : Set ℓ} → refl A ≡ ua ref≃
ref≡ {ℓ} {A} with isequiv→qinv (univalence {A = A} {B = A})
ref≡ {ℓ} {A} | idtoeqv⁻¹ , (α , β) = refl A
                                   ≡⟨ β (refl A) ⁻¹ ⟩
                                     idtoeqv⁻¹ (idtoeqv (refl A))
                                   ≡⟨ ap idtoeqv⁻¹ (refl ref≃) ⟩
                                     (idtoeqv⁻¹ ref≃) ∎

▪≡' : ∀ {ℓ} {A B C : Set ℓ} (p : A ≡ B) (q : B ≡ C) → (idtoeqv (p ▪ q)) ≡ (idtoeqv q ○ idtoeqv p)
▪≡' {ℓ} {A} {B} {C} p q = ind≡ (λ A B p → (C : Set ℓ) → (q : B ≡ C)
                                        → (idtoeqv (p ▪ q)) ≡ (idtoeqv q ○ idtoeqv p))
                               (λ A C q → ind≡ (λ A C q → (idtoeqv ((refl A) ▪ q)) ≡ (idtoeqv q ○ idtoeqv (refl A)))
                                               (λ A → refl (idtoeqv (refl A)))
                                               A C q)
                               A B p C q

▪≡ : ∀ {ℓ} {A B C : Set ℓ} (f : A ≃ B) (g : B ≃ C) → (ua f) ▪ (ua g) ≡ ua (g ○ f)
▪≡ {ℓ} {A} {B} {C} f g =
      ua f ▪ ua g
   ≡⟨ uniq≡ (ua f ▪ ua g) ⟩
      ua (idtoeqv (ua f ▪ ua g))
   ≡⟨ ap ua (▪≡' (ua f) (ua g)) ⟩
      ua (idtoeqv (ua g) ○ idtoeqv (ua f))
   ≡⟨ ap (λ r → ua (r ○ idtoeqv (ua f))) ((comp≡ g) ⁻¹) ⟩
      ua (g ○ idtoeqv (ua f))
   ≡⟨ ap (λ r → ua (g ○ r)) (comp≡ f ⁻¹) ⟩
      ua (g ○ f) ∎

≡⁻¹' : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) → idtoeqv (p ⁻¹) ≡ (idtoeqv p) ⁻¹≃
≡⁻¹' {ℓ} {A} {B} p = ind≡ (λ A B p → idtoeqv (p ⁻¹) ≡ (idtoeqv p) ⁻¹≃)
                          (λ A → refl (idtoeqv (refl A)))
                          A B p

≡⁻¹ : ∀ {ℓ} {A B : Set ℓ} (f : A ≃ B) → (ua f) ⁻¹ ≡ ua (f ⁻¹≃)
≡⁻¹ {ℓ} {A} {B} f =  (ua f ⁻¹)
                  ≡⟨ uniq≡ ((ua f) ⁻¹) ⟩
                     ua (idtoeqv ((ua f) ⁻¹))
                  ≡⟨ ap (λ p → ua p) (≡⁻¹' (ua f)) ⟩
                     ua ((idtoeqv (ua f)) ⁻¹≃)
                  ≡⟨ ap (λ p → ua (p ⁻¹≃)) ((comp≡ f) ⁻¹) ⟩
                     ua (f ⁻¹≃) ∎

--Lemma 2.10.5
transport≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {x y : A} →
             (p : x ≡ y) (u : B x) → transport B p u ≡ (pr₁ (idtoeqv (ap B p))) u
transport≡ {ℓ} {ℓ'} {A} {B} {x} {y} p u =
           transport ((λ x → x) ∘ B) p u
        ≡⟨ transport[P∘f,p,u]≡transport[P,ap[f,p],u] B (λ x₁ → x₁) p u ⟩
           transport (λ x → x) (ap B p) u
        ≡⟨ ap (λ f → (f (ap B p)) u) elim≡ ⟩
          (pr₁ (idtoeqv (ap B p))) u ∎
