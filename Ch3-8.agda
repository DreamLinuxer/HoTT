{-# OPTIONS --without-K #-}
module Ch3-8 where
open import Base
open import Ch3-1
open import Ch3-3
open import Ch3-7
open import Level

AC : ∀ {ℓ ℓ' ℓ''} → Set _
AC {ℓ} {ℓ'} {ℓ''} =
   {X : Set ℓ} {A : X → Set ℓ'} {P : (x : X) → A x → Set ℓ''} →
   {XisSet : isSet X} {AisSet : (x : X) → isSet (A x)} {PisProp : (x : X) (a : A x) → isProp (P x a)} →
   ((x : X) → ∥ Σ[ a ∈ (A x) ] (P x a) ∥) → ∥ Σ[ g ∈ ((x : X) → A x) ] ((x : X) → P x (g x)) ∥

AC' : ∀ {ℓ ℓ'} → Set _
AC' {ℓ} {ℓ'} =
    {X : Set ℓ} {Y : X → Set ℓ'} →
    {XisSet : isSet X} {YisSet : (x : X) → isSet (Y x)} →
    ((x : X) → ∥ Y x ∥) → ∥ ((x : X) → Y x) ∥

--Lemma 3.8.2
AC→AC' : ∀ {ℓ ℓ'} → AC → AC' {ℓ} {ℓ'}
AC→AC' ac {X} {Y} {XisSet} {YisSet} f =
       pr₁ (rec∥-∥ inhabPath (λ {(g , _) → ∣ g ∣})) choice
       where
       g : (x : X) → ∥ Σ (Y x) (λ _ → 𝟙) ∥
       g x = pr₁ (rec∥-∥ inhabPath (λ Yx → ∣ Yx , ⋆ ∣)) (f x)
       
       choice : ∥ Σ[ g ∈ ((x : X) → Y x) ] ((x : X) → 𝟙) ∥
       choice = ac {X} {Y} {λ _ _ → 𝟙} {XisSet} {YisSet} {λ { _ _ ⋆ ⋆ → refl ⋆ }} g

AC'→AC : ∀ {ℓ ℓ' ℓ''} → AC' → AC {ℓ} {ℓ'} {ℓ''}
AC'→AC ac' {X} {A} {P} {XisSet} {AisSet} {PisProp} f =
       pr₁ (rec∥-∥ inhabPath (λ g → ∣ (λ x → pr₁ (g x)) , (λ x → pr₂ (g x)) ∣)) choice
       where
       choice : ∥ ((x : X) → Σ[ a ∈ (A x) ] (P x a)) ∥
       choice = ac' {X} {λ x → Σ[ a ∈ (A x) ] (P x a)} {XisSet}
                    {λ x → ΣisSet {AisSet = AisSet x} {BisSet = λ a → PropisSet (PisProp x a)}} f

𝟚isSet : isSet 𝟚
𝟚isSet 0₂ 0₂ (refl .0₂) (refl .0₂) = refl (refl 0₂)
𝟚isSet 0₂ 1₂ () ()
𝟚isSet 1₂ 0₂ () ()
𝟚isSet 1₂ 1₂ (refl .1₂) (refl .1₂) = refl (refl 1₂)

module lemma3-8-5 where
  X : Set _
  X = Σ[ A ∈ Set ] ∥ 𝟚 ≡ A ∥

  x₀ : X
  x₀ = 𝟚 , ∣ refl 𝟚 ∣

  postulate
    isequivIsProp : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → isProp (isequiv f) 

  eq : (X₁ X₂ : X) → (X₁ ≡ X₂) ≃ (pr₁ X₁ ≃ pr₁ X₂)
  eq (A , p) (B , q) = f , qinv→isequiv (g , α , β)
     where
     f : (A , p ≡ B , q) → A ≃ B
     f (refl _) = idtoeqv (refl _)

     g : A ≃ B → (A , p ≡ B , q)
     g eq = pairΣ≡ (ua eq , inhabPath _ _)

     α : f ∘ g ~ id
     α eq = pairΣ≡ ( f-pr₁ (g eq) ▪ ap (transport id) (pairΣ≡₁ (ua eq , inhabPath _ _)) ▪ funext (computation≡ eq)
                   , isequivIsProp _ _ _)
            where
            f-pr₁ : (w : A , p ≡ B , q)
                  → pr₁ (f w) ≡ transport id (ap pr₁ w)
            f-pr₁ (refl _) = refl _

            pairΣ≡₁ : {A B : Set} {p : ∥ 𝟚 ≡ A ∥} {q : ∥ 𝟚 ≡ B ∥}
                    → (w : Σ[ w₁ ∈ A ≡ B ] transport _ w₁ p ≡ q)
                    → ap pr₁ (pairΣ≡ {w = A , p} {w' = B , q} w) ≡ pr₁ w
            pairΣ≡₁ (refl _ , refl _) = refl (refl _)

     β : g ∘ f ~ id
     β (refl _) = ap pairΣ≡ (pairΣ≡ ((uniq≡ _)⁻¹ , (PropisSet inhabPath _ _ _ _)))

  Ωx₀≃[𝟚≃𝟚] : (x₀ ≡ x₀) ≃ (𝟚 ≃ 𝟚)
  Ωx₀≃[𝟚≃𝟚] = eq _ _

  ¬XisSet : ¬ (isSet X)
  ¬XisSet XisSet = 0₂≠1₂ (ap (λ f → f 1₂) (ap pr₁ f≃≡id≃))
    where
    𝟚≃𝟚isProp : isProp (𝟚 ≃ 𝟚)
    𝟚≃𝟚isProp eq₁ eq₂ with Ωx₀≃[𝟚≃𝟚]
    ... | f , eq with isequiv→qinv eq
    ... | g , α , β = α eq₁ ⁻¹ ▪ ap f (XisSet _ _ _ _) ▪ α eq₂

    f : 𝟚 → 𝟚
    f 0₂ = 1₂
    f 1₂ = 0₂

    f≃ : isequiv f
    f≃ = (f , (ind𝟚 (λ b → f (f b) ≡ b) (refl 0₂) (refl 1₂)))
       , (f , (ind𝟚 (λ b → f (f b) ≡ b) (refl 0₂) (refl 1₂)))

    f≃≡id≃ : (f , f≃) ≡ (idtoeqv (refl 𝟚))
    f≃≡id≃ with isequiv→qinv (univalence {A = 𝟚} {B = 𝟚})
    f≃≡id≃ | idtoeqv⁻¹ , α , β =
           (f , f≃) ≡⟨ α (f , f≃) ⁻¹ ⟩
           (idtoeqv (idtoeqv⁻¹ (f , f≃))) ≡⟨ 𝟚≃𝟚isProp _ _ ⟩
           (idtoeqv (idtoeqv⁻¹ (idtoeqv (refl 𝟚)))) ≡⟨ α (idtoeqv (refl 𝟚)) ⟩
           idtoeqv (refl 𝟚) ∎

  ≃isSet : {A B : Set} → isSet A → isSet B → isSet (A ≃ B)
  ≃isSet AisSet BisSet = ΣisSet {AisSet = ΠisSet {BxisSet = λ _ → BisSet}}
                                {BisSet = λ f → PropisSet (isequivIsProp f)}

  X₁isSet : (x : X) → isSet (pr₁ x)
  X₁isSet (A , p) = pr₁ (rec∥-∥ isSetAisProp f) p
          where
          f : 𝟚 ≡ A → isSet A
          f p = transport isSet p 𝟚isSet

  Xis1-type : 1-type X
  Xis1-type {x = (A , p)} {y = (B , q)} = transport isSet ([x≡y]≡[A≃B] ⁻¹) L[A≃B]isSet _ _
    where
    [A≃B]≃L[A≃B] : (A ≃ B) ≃ (Lift (A ≃ B))
    [A≃B]≃L[A≃B] = Level.lift , qinv→isequiv (Level.lower , refl , refl)

    [x≡y]≡[A≃B] : (A , p ≡ B , q) ≡ Lift (A ≃ B)
    [x≡y]≡[A≃B] = ua (tran≃ (eq _ _) [A≃B]≃L[A≃B])

    L[A≃B]isSet : isSet (Lift (A ≃ B))
    L[A≃B]isSet eq₁ eq₂ p₁ p₂ =
                p₁ ≡⟨ lem p₁ ⟩
                ap Level.lift (ap lower p₁) ≡⟨ ap (ap Lift.lift) (≃isSet (X₁isSet (A , p)) (X₁isSet (B , q)) _ _ _ _)  ⟩
                ap Level.lift (ap lower p₂) ≡⟨ (lem p₂) ⁻¹  ⟩
                p₂ ∎
                where
                lem : (r : eq₁ ≡ eq₂) → r ≡ ap Level.lift (ap lower r)
                lem r = apid _ _ r ⁻¹ ▪ (ap∘ lower Level.lift _ _ r) ⁻¹

  Y : X → Set _
  Y x = x₀ ≡ x

  YisSet : (x : X) → isSet (Y x)
  YisSet x p q r s = Xis1-type r s

  𝒇 : (x : X) → ∥ Y x ∥
  𝒇 (A , p) = pr₁ (rec∥-∥ inhabPath (λ p → ∣ pairΣ≡ (p , inhabPath _ _) ∣)) p

  AC'' : ∀ {ℓ ℓ'} → Set _
  AC'' {ℓ} {ℓ'} = {X : Set ℓ} {Y : X → Set ℓ'}
               → {YisSet : (x : X) → isSet (Y x)}
               → ((x : X) → ∥ Y x ∥) → ∥ ((x : X) → Y x) ∥

  ¬AC'' : ¬ AC''
  ¬AC'' ac = ¬XisSet (PropisSet XisProp)
        where
        contra : ∥ ((x : X) → Y x) ∥
        contra = ac {X} {Y} {YisSet} 𝒇
        
        XisProp : isProp X
        XisProp = pr₁ (rec∥-∥ isPropAisProp (λ f x₁ x₂ → (f x₁)⁻¹ ▪ f x₂)) contra
