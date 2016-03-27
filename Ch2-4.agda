{-# OPTIONS --without-K #-}

module Ch2-4 where
open import Ch2-3 public

--2.4
infix 2 _~_

_~_ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_~_ {A = A} f g = (x : A) → f x ≡ g x

--Lemma 2.4.2
ref~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → f ~ f
ref~ f = λ x → ap f (refl x)

sym~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → f ~ g → g ~ f
sym~ {ℓ} {ℓ'} {A} {B} {f} {g} f~g = λ x → (f~g x) ⁻¹

tran~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g h : A → B} → f ~ g → g ~ h → f ~ h
tran~ {ℓ} {ℓ'} {A} {B} {f} {g} {h} f~g g~h = λ x → (f~g x) ▪ (g~h x)

--Lemma 2.4.3
ntran~ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f g : A → B) (H : f ~ g) {x y : A} (p : x ≡ y) →
         H x ▪ ap g p ≡ ap f p ▪ H y
ntran~ {ℓ} {ℓ'} {A} {B} f g H {x} {y} p = ind≡ (λ x y p → H x ▪ ap g p ≡ ap f p ▪ H y)
                                               (λ x → ((unit-right (H x)) ⁻¹) ▪ (unit-left (H x)))
                                               x y p

--Corollary 2.4.4
comm~' : ∀ {ℓ} {A : Set ℓ} (f : A → A) (H : f ~ id) (x : A) →
         H (f x) ▪ H x ≡ ap f (H x) ▪ H x
comm~' {ℓ} {A} f H x = (H (f x) ▪ H x)
                     ≡⟨ ap (λ p → H (f x) ▪ p) (apid (f x) x (H x) ⁻¹) ⟩
                       H (f x) ▪ ap id (H x)
                     ≡⟨ ntran~ f id H (H x) ⟩
                       (ap f (H x) ▪ H x ∎)

comm~ : ∀ {ℓ} {A : Set ℓ} (f : A → A) (H : f ~ id) (x : A) →
        H (f x) ≡ ap f (H x)
comm~ {ℓ} {A} f H x = H (f x)
                    ≡⟨ unit-right (H (f x)) ⟩
                      H (f x) ▪ refl (f x)
                    ≡⟨ ap (λ p → H (f x) ▪ p) (p▪p⁻¹≡reflx (H x)) ⁻¹ ⟩
                      H (f x) ▪ (H x ▪ H x ⁻¹)
                    ≡⟨ assoc▪ (H (f x)) (H x) (H x ⁻¹)⟩
                      H (f x) ▪ H x ▪ H x ⁻¹
                    ≡⟨ ap (λ p → p ▪ H x ⁻¹) (comm~' f H x) ⟩
                      ap f (H x) ▪ H x ▪ H x ⁻¹
                    ≡⟨ assoc▪ (ap f (H x)) (H x) (H x ⁻¹) ⁻¹ ⟩
                      ap f (H x) ▪ (H x ▪ H x ⁻¹)
                    ≡⟨ ap (λ p → ap f (H x) ▪ p) (p▪p⁻¹≡reflx (H x)) ⟩
                      ap f (H x) ▪ refl (f x)
                    ≡⟨ unit-right (ap f (H x)) ⁻¹ ⟩
                      ap f (H x) ∎

--Definition 2.4.6
qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
qinv {ℓ} {ℓ'} {A} {B} f = Σ[ g ∈ (B → A) ] (f ∘ g ~ id) × (g ∘ f ~ id)

--Example 2.4.7
qinvId : {A : Set} → qinv {A = A} id
qinvId = id , ((λ y → refl y) , (λ x → refl x))

--Example 2.4.8
qinv≡₁ : {A : Set} {x y : A} (p : x ≡ y) (z : A) → qinv {A = y ≡ z} {B = x ≡ z} (λ q → p ▪ q)
qinv≡₁ {A} {x} {y} p z = (λ q → p ⁻¹ ▪ q)
                       , ( (λ q → p ▪ (p ⁻¹ ▪ q)
                                ≡⟨ assoc▪ p (p ⁻¹) q ⟩
                                  p ▪ p ⁻¹ ▪ q
                                ≡⟨ ap (λ p → p ▪ q) (p▪p⁻¹≡reflx p) ⟩
                                  refl x ▪ q
                                ≡⟨ (unit-left q) ⁻¹ ⟩
                                  q ∎)
                         , (λ q → p ⁻¹ ▪ (p ▪ q)
                                ≡⟨ assoc▪ (p ⁻¹) p q ⟩
                                  p ⁻¹ ▪ p ▪ q
                                ≡⟨ ap (λ p₁ → p₁ ▪ q) (p⁻¹▪p≡refly p) ⟩
                                  refl y ▪ q
                                ≡⟨ (unit-left q) ⁻¹ ⟩
                                   q ∎))

qinv≡₂ : {A : Set} {x y : A} (p : x ≡ y) (z : A) → qinv {A = z ≡ x} {B = z ≡ y} (λ q → q ▪ p)
qinv≡₂ {A} {x} {y} p z = (λ q → q ▪ p ⁻¹)
                       , ( (λ q → q ▪ p ⁻¹ ▪ p
                                ≡⟨ (assoc▪ q (p ⁻¹) p) ⁻¹ ⟩
                                  q ▪ (p ⁻¹ ▪ p)
                                ≡⟨ ap (λ p → q ▪ p) (p⁻¹▪p≡refly p) ⟩
                                  q ▪ refl y
                                ≡⟨ (unit-right q) ⁻¹ ⟩
                                   q ∎)
                         , (λ q → q ▪ p ▪ p ⁻¹
                                ≡⟨ (assoc▪ q p (p ⁻¹)) ⁻¹ ⟩
                                   q ▪ (p ▪ p ⁻¹)
                                ≡⟨ ap (λ p → q ▪ p) (p▪p⁻¹≡reflx p) ⟩
                                   q ▪ refl x
                                ≡⟨ (unit-right q) ⁻¹ ⟩
                                   q ∎))

qinv≡₃ : {A : Set} {x y : A} (P : A → Set) (p : x ≡ y) →
         qinv {A = P x} {B = P y} (transport P p)
qinv≡₃ {A} {x} {y} P p = (transport P (p ⁻¹))
                       , ((λ z → (p *) ((p ⁻¹ *) z)
                               ≡⟨ q*[p*[u]]≡[[p▪q]*][u] P (p ⁻¹) p z ⟩
                                 ((p ⁻¹ ▪ p) *) z
                               ≡⟨ ap (λ p → (p *) z) (p⁻¹▪p≡refly p) ⟩
                                 z ∎)
                       ,  (λ z → ((p ⁻¹) *) ((p *) z)
                               ≡⟨ q*[p*[u]]≡[[p▪q]*][u] P p (p ⁻¹) z ⟩
                                 ((p ▪ p ⁻¹) *) z
                               ≡⟨ ap (λ p → (p *) z) (p▪p⁻¹≡reflx p) ⟩
                                 z ∎))

isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
isequiv {ℓ} {ℓ'} {A} {B} f = (Σ[ g ∈ (B → A) ] (f ∘ g ~ id) ) × (Σ[ h ∈ (B → A) ] (h ∘ f ~ id) )

qinv→isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               qinv f → isequiv f
qinv→isequiv (g , (α , β))= (g , α) , (g , β)

isequiv→qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               isequiv f → qinv f
isequiv→qinv {f = f} ((g , α) , (h , β)) =
             let γ : g ~ h
                 γ x = (β (g x) ⁻¹) ▪ (ap h (α x))
             in  g , (α , (λ x → (γ (f x)) ▪ (β x)))

infix 2 _≃_
_≃_ : ∀ {ℓ} {ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

--Lemma 2.4.12
ref≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
ref≃ = id , ((id , refl) , (id , refl))

sym≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
sym≃ (f , eq) with (isequiv→qinv eq)
sym≃ (f , eq) | (f⁻¹ , (α , β)) = f⁻¹ , ((f , β) , (f , α))

tran≃ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
        A ≃ B → B ≃ C → A ≃ C
tran≃ (f , eq1) (g , eq2) with (isequiv→qinv eq1)
tran≃ (f , eq1) (g , eq2) | (f⁻¹ , (α1 , β1)) with (isequiv→qinv eq2)
tran≃ (f , eq1) (g , eq2) | (f⁻¹ , (α1 , β1)) | (g⁻¹ , (α2 , β2)) =
      (g ∘ f) , ((f⁻¹ ∘ g⁻¹ , (λ x → g (f (f⁻¹ (g⁻¹ x)))
                                   ≡⟨ ap (λ y → g y) (α1 (g⁻¹ x)) ⟩
                                     g (g⁻¹ x)
                                   ≡⟨ α2 x ⟩
                                     x ∎))
              ,  (f⁻¹ ∘ g⁻¹ , (λ x → f⁻¹ (g⁻¹ (g (f x)))
                                   ≡⟨ ap (λ y → f⁻¹ y) (β2 (f x)) ⟩
                                     f⁻¹ (f x)
                                   ≡⟨ β1 x ⟩
                                     x ∎)))

infix 3 _○_
_○_ : ∀ {ℓ} {ℓ'} {ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
      (f : B ≃ C) (g : A ≃ B) → A ≃ C
g ○ f  = tran≃ f g

infix 20 _⁻¹≃
_⁻¹≃ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A ≃ B) → B ≃ A
_⁻¹≃ f = sym≃ f
