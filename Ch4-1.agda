{-# OPTIONS --without-K #-}
module Ch4-1 where
open import Base
open import Ch3-1
open import Ch3-3
open import Ch3-7
open import Ch3-8
open import Ch3-11
open import Ex2
open import Ex3

-- Lemma 4.1.1
qinv≃Π[x≡x] : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → qinv f
           → qinv f ≃ ((x : A) → x ≡ x)
qinv≃Π[x≡x] {A = A} {B} 𝒇 qe = lem (𝒇 , qinv→isequiv qe)
  where
  eq₁ : (qinv id) ≃ (Σ[ g ∈ (A → A) ] ((g ≡ id) × (g ≡ id)))
  eq₁ = (λ {(g , α , β) → g , funext α , funext β})
      , qinv→isequiv ((λ {(g , p , q) → g , happly p , happly q})
                   ,  (λ {(g , p , q) → ap (λ x → g , x , (funext (happly q))) (uniqΠ≡ p)
                                      ▪ ap (λ x → g , p , x) (uniqΠ≡ q)})
                   ,  (λ {(g , α , β) → ap (λ x → g , x , (happly (funext β))) (compΠ≡ α)
                                      ▪ ap (λ x → g , α , x) (compΠ≡ β)}))

  eq₂ : (Σ[ g ∈ (A → A) ] ((g ≡ id) × (g ≡ id))) ≃ (Σ[ h ∈ (Σ[ g ∈ (A → A) ] (id ≡ g)) ] (pr₁ h ≡ id))
  eq₂ = (λ {(g , p , q) → (g , p ⁻¹) , q})
      , qinv→isequiv ((λ {((g , p) , q) → g , p ⁻¹ , q})
                   ,  (λ {((g , p) , q) → ap (λ x → ((g , x) , q)) (p⁻¹⁻¹≡p p)})
                   ,  (λ {(g , p , q) → ap (λ x → (g , x , q)) (p⁻¹⁻¹≡p p)}))

  eq₃ : (Σ[ h ∈ (Σ[ g ∈ (A → A) ] (id ≡ g)) ] (pr₁ h ≡ id)) ≃ (id ≡ id)
  eq₃ = isContrA→ΣPx≃Pa _ _ (Σ[a≡x]isContr (A → A) id)

  eq₄ : (id ≡ id) ≃ ((x : A) → x ≡ x)
  eq₄ = happly , funextentionality
  
  lem' : (p : A ≡ B) → qinv (pr₁ (idtoeqv p)) ≃ ((x : A) → x ≡ x)
  lem' (refl _) = tran≃ eq₁ (tran≃ eq₂ (tran≃ eq₃ eq₄))

  lem : (e : A ≃ B) → qinv (pr₁ e) ≃ ((x : A) → x ≡ x)
  lem e = idtoeqv (transport (λ x → (qinv ∘ pr₁) x  ≡ ((x : A) → x ≡ x))
                             (comp≡ e ⁻¹) (ua (lem' (ua e))))

-- Lemma 4.1.2
∃Π[x≡x] : ∀ {ℓ} {A : Set ℓ} → (a : A) → (q : a ≡ a)
        → isSet (a ≡ a) → ((x : A) → ∥ a ≡ x ∥)
        → ((p : a ≡ a) → p ▪ q ≡ q ▪ p)
        → Σ[ f ∈ ((x : A) → x ≡ x) ] f a ≡ q
∃Π[x≡x] {ℓ} {A} a q [a≡a]isSet g commq = (λ x → pr₁ (x→Bx x)) , fa≡q
  where
  [x≡y]≃[a≡a] : (x y : A) → a ≡ x → a ≡ y → (x ≡ y) ≃ (a ≡ a)
  [x≡y]≃[a≡a] x y p q = (λ r → p ▪ r ▪ q ⁻¹)
                      , qinv→isequiv ((λ r → p ⁻¹ ▪ r ▪ q) , α , β)
    where
    α : (r : a ≡ a) → p ▪ (p ⁻¹ ▪ r ▪ q) ▪ q ⁻¹ ≡ r
    α r = p ▪ (p ⁻¹ ▪ r ▪ q) ▪ q ⁻¹ ≡⟨ ap (λ x → x ▪ q ⁻¹) (assoc▪ _ _ _) ⟩
          p ▪ (p ⁻¹ ▪ r) ▪ q ▪ q ⁻¹ ≡⟨ ap (λ x → x ▪ q ▪ q ⁻¹) (assoc▪ _ _ _) ⟩
          p ▪ p ⁻¹ ▪ r ▪ q ▪ q ⁻¹ ≡⟨ ap (λ x → x ▪ r ▪ q ▪ q ⁻¹) (p▪p⁻¹≡reflx _) ⟩
          refl _ ▪ r ▪ q ▪ q ⁻¹ ≡⟨ ap (λ x₁ → x₁ ▪ q ▪ q ⁻¹) (unit-left _ ⁻¹) ⟩
          r ▪ q ▪ q ⁻¹ ≡⟨ assoc▪ _ _ _ ⁻¹ ⟩
          r ▪ (q ▪ q ⁻¹) ≡⟨ ap (_▪_ r) (p▪p⁻¹≡reflx _) ⟩
          r ▪ refl _ ≡⟨ unit-right _ ⁻¹ ⟩
          r ∎

    β : (r : x ≡ y) → p ⁻¹ ▪ (p ▪ r ▪ q ⁻¹) ▪ q ≡ r
    β r = p ⁻¹ ▪ (p ▪ r ▪ q ⁻¹) ▪ q ≡⟨ ap (λ x₁ → x₁ ▪ q) (assoc▪ _ _ _) ⟩
          p ⁻¹ ▪ (p ▪ r) ▪ q ⁻¹ ▪ q ≡⟨ ap (λ x₁ → x₁ ▪ q ⁻¹ ▪ q) (assoc▪ _ _ _) ⟩
          p ⁻¹ ▪ p ▪ r ▪ q ⁻¹ ▪ q ≡⟨ ap (λ x₁ → x₁ ▪ r ▪ q ⁻¹ ▪ q) (p⁻¹▪p≡refly _) ⟩
          refl _ ▪ r ▪ q ⁻¹ ▪ q ≡⟨ ap (λ x₁ → x₁ ▪ q ⁻¹ ▪ q) (unit-left _ ⁻¹) ⟩
          r ▪ q ⁻¹ ▪ q ≡⟨ assoc▪ _ _ _ ⁻¹ ⟩
          r ▪ (q ⁻¹ ▪ q) ≡⟨ ap (_▪_ r) (p⁻¹▪p≡refly _) ⟩
          r ▪ refl _ ≡⟨ unit-right _ ⁻¹ ⟩
          r ∎

  [x≡y]isSet : (x y : A) → isSet (x ≡ y)
  [x≡y]isSet x y = rec∥-∥ isSetAisProp
                               (λ p → rec∥-∥ isSetAisProp
                                            (λ q → Ex3-1.≃isSet [a≡a]isSet
                                                   (sym≃ ([x≡y]≃[a≡a] x y p q))) (g y)) (g x)

  B : A → Set _
  B x = Σ[ r ∈ (x ≡ x) ] ((s : a ≡ x) → r ≡ s ⁻¹ ▪ q ▪ s)

  BisProp : (x : A) → isProp (B x)
  BisProp x = rec∥-∥ isPropAisProp
                    (λ {p (r , h) (r' , h') → pairΣ≡ (h p ▪ h' p ⁻¹ ,
                                                      funext (λ s → [x≡y]isSet _ _ _ _ _ _))}) (g x)
  x→Bx : (x : A) → B x
  x→Bx x = rec∥-∥ (BisProp x) (λ p → (p ⁻¹ ▪ q ▪ p)
                                  , (λ s → β s p)) (g x)
           where
           α : (s p : a ≡ x) → q ▪ p ▪ s ⁻¹ ≡ p ▪ s ⁻¹ ▪ q
           α s p = assoc▪ _ _ _ ⁻¹ ▪ commq (p ▪ s ⁻¹) ⁻¹

           β : (s p : a ≡ x) → p ⁻¹ ▪ q ▪ p ≡ s ⁻¹ ▪ q ▪ s
           β s p = p ⁻¹ ▪ q ▪ p ≡⟨ unit-right _ ⟩
                   p ⁻¹ ▪ q ▪ p ▪ refl _ ≡⟨ ap (λ x → p ⁻¹ ▪ q ▪ p ▪ x) (p⁻¹▪p≡refly _ ⁻¹) ⟩
                   p ⁻¹ ▪ q ▪ p ▪ (s ⁻¹ ▪ s) ≡⟨ assoc▪ _ _ _ ⟩
                   p ⁻¹ ▪ q ▪ p ▪ s ⁻¹ ▪ s ≡⟨ ap (λ x → x ▪ s ⁻¹ ▪ s) (assoc▪ _ _ _ ⁻¹) ⟩
                   p ⁻¹ ▪ (q ▪ p) ▪ s ⁻¹ ▪ s ≡⟨ ap (λ x₁ → x₁ ▪ s) (assoc▪ _ _ _ ⁻¹) ⟩
                   p ⁻¹ ▪ (q ▪ p ▪ s ⁻¹) ▪ s ≡⟨ ap (λ x₁ → p ⁻¹ ▪ x₁ ▪ s) (α s p) ⟩
                   p ⁻¹ ▪ (p ▪ s ⁻¹ ▪ q) ▪ s ≡⟨ ap (λ x₁ → x₁ ▪ s) (assoc▪ _ _ _) ⟩
                   p ⁻¹ ▪ (p ▪ s ⁻¹) ▪ q ▪ s ≡⟨ ap (λ x₁ → x₁ ▪ q ▪ s) (assoc▪ _ _ _) ⟩
                   p ⁻¹ ▪ p ▪ s ⁻¹ ▪ q ▪ s ≡⟨ ap (λ x₁ → x₁ ▪ s ⁻¹ ▪ q ▪ s) (p⁻¹▪p≡refly _) ⟩
                   refl _ ▪ s ⁻¹ ▪ q ▪ s ≡⟨ ap (λ x₁ → x₁ ▪ q ▪ s) (unit-left _ ⁻¹) ⟩
                   s ⁻¹ ▪ q ▪ s ∎

  fa≡q : pr₁ (x→Bx a) ≡ q
  fa≡q = pr₂ (x→Bx a) q ▪ ap (λ x → x ▪ q) (p⁻¹▪p≡refly _) ▪ unit-left _ ⁻¹

-- Theorem 4.1.3
∃[¬isProp[qinvf]] : Σ[ eq ∈ (Σ[ T ∈ Set _ × Set _ ] (pr₁ T → pr₂ T)) ] (¬ isProp (qinv (pr₂ eq)))
∃[¬isProp[qinvf]] = ((X , X) , id)
                  , transport (λ x → ¬ isProp x)
                              (ua (qinv≃Π[x≡x] id (id , refl , refl)) ⁻¹) ¬isPropΠ[x≡x]
  where
  open Ex2-13
  
  X : Set _
  X = Σ[ A ∈ Set ] ∥ 𝟚 ≡ A ∥

  a : X
  a = 𝟚 , ∣ refl 𝟚 ∣

  q : a ≡ a
  q = pairΣ≡ (ua not≃ , inhabPath _ _)

  [a≡a]≃[𝟚≃𝟚] : (a ≡ a) ≃ (𝟚 ≃ 𝟚)
  [a≡a]≃[𝟚≃𝟚] = lemma3-8-5.eq a a

  q≠refl : ¬ (q ≡ refl a)
  q≠refl q≡refl = 0₂≠1₂ (ap (λ f → f 1₂) (ap pr₁ not≃≡id≃))
    where
    uanot≃≡refl : (ua not≃) ≡ refl 𝟚
    uanot≃≡refl = ua not≃ ≡⟨ pairΣ≡₁ (ua not≃ , inhabPath _ _) ⁻¹ ⟩
                  ap pr₁ q ≡⟨ ap (ap pr₁) q≡refl ⟩
                  refl 𝟚 ∎

    not≃≡id≃ : not≃ ≡ (idtoeqv (refl 𝟚))
    not≃≡id≃ = not≃ ≡⟨ comp≡ not≃ ⟩
               idtoeqv (ua not≃) ≡⟨ ap idtoeqv uanot≃≡refl ⟩
               idtoeqv (refl 𝟚) ∎

  lem : (p : a ≡ a) → (pr₁ [a≡a]≃[𝟚≃𝟚] p ≡ pr₁ [a≡a]≃[𝟚≃𝟚] q)
      → p ▪ q ≡ q ▪ p
  lem p r = (ap (_▪_ p) (p≡q ⁻¹)) ▪ (ap (λ x → x ▪ p) p≡q)
    where
    p≡q : p ≡ q
    p≡q = pr₂ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚])) p ⁻¹
        ▪ ap (pr₁ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚]))) r
        ▪ pr₂ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚])) q

  p▪q≡q▪p : (ep eq : 𝟚 ≃ 𝟚) (p : a ≡ a)
          → pr₁ [a≡a]≃[𝟚≃𝟚] p ≡ ep → pr₁ [a≡a]≃[𝟚≃𝟚] q ≡ eq
          → p ▪ q ≡ q ▪ p
  p▪q≡q▪p ep eq p r s with [𝟚≃𝟚]≡id∨not ep | [𝟚≃𝟚]≡id∨not eq
  p▪q≡q▪p ep eq p r s | inl ep≡refl≃ | inl eq≡refl≃ = lem p (r ▪ ep≡refl≃ ▪ eq≡refl≃ ⁻¹ ▪ s ⁻¹)
  p▪q≡q▪p ep eq p r s | inl ep≡refl≃ | inr eq≡not≃  =
    ap (λ x → x ▪ q) p≡refl ▪ unit-left q ⁻¹ ▪ unit-right q ▪ ap (λ x → q ▪ x) (p≡refl ⁻¹)
    where
    p≡refl : p ≡ refl a
    p≡refl = (pr₂ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚])) p) ⁻¹
           ▪ ap (pr₁ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚]))) r
           ▪ ap (pr₁ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚]))) ep≡refl≃
           ▪ (pr₂ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚])) (refl a))
  p▪q≡q▪p ep eq p r s | inr ep≡not≃  | inl eq≡refl≃ = rec𝟘 _ (q≠refl q≡refl)
    where
    q≡refl : q ≡ refl a
    q≡refl = (pr₂ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚])) q) ⁻¹
           ▪ ap (pr₁ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚]))) s
           ▪ ap (pr₁ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚]))) eq≡refl≃
           ▪ pr₂ (pr₂ (pr₂ [a≡a]≃[𝟚≃𝟚])) (refl a)
  p▪q≡q▪p ep eq p r s | inr ep≡not≃  | inr eq≡not≃  = lem p (r ▪ ep≡not≃ ▪ eq≡not≃ ⁻¹ ▪ s ⁻¹)

  Σf : Σ[ f ∈ ((x : X) → x ≡ x) ] (f a ≡ q)
  Σf = ∃Π[x≡x] a q (λ p q r s → lemma3-8-5.Xis1-type r s)
               (λ {(τ , p) → rec∥-∥ inhabPath (λ p → ∣ pairΣ≡ (p , (inhabPath _ _)) ∣) p})
               (λ p → p▪q≡q▪p (pr₁ [a≡a]≃[𝟚≃𝟚] p) (pr₁ [a≡a]≃[𝟚≃𝟚] q) p (refl _) (refl _))

  f : (x : X) → x ≡ x
  f = pr₁ Σf

  f≠refl : ¬ (f ≡ λ x → refl x)
  f≠refl f≡refl = q≠refl (pr₂ Σf ⁻¹ ▪ ap (λ g → g a) f≡refl)

  ¬isPropΠ[x≡x] : ¬ isProp ((x : X) → x ≡ x)
  ¬isPropΠ[x≡x] Π[x≡x]isProp = f≠refl (Π[x≡x]isProp _ _)
