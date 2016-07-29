module Ch3-1 where
open import Base
open Σ

-- Definition 3.1.1
isSet : ∀ {ℓ} (A : Set ℓ) → Set _
isSet A = {x y : A} → (p q : x ≡ y) → p ≡ q

-- Example 3.1.2
𝟙isSet : isSet 𝟙
𝟙isSet {x} {y} p q with 𝟙≃ {x} {y}
𝟙isSet {x} {y} p q | f , mkisequiv g α h β =
       p       ≡⟨ β p ⁻¹ ⟩
       h (f p) ≡⟨ ap h (uniq𝟙 (f p)) ⟩
       h ⊤     ≡⟨ ap h (uniq𝟙 (f q) ⁻¹) ⟩
       h (f q) ≡⟨ (β q) ⟩
       q ∎

-- Example 3.1.3
𝟘isSet : isSet 𝟘
𝟘isSet {x} = ind𝟘 (λ x → isSet 𝟘) x

-- Example 3.1.4
ℕisSet : isSet ℕ
ℕisSet {m} {n} p q with ℕ≃ {m} {n}
ℕisSet {m} {n} p q | f , mkisequiv g α h β =
       β p ⁻¹ ▪ ((ap h (uniq {m = m})) ▪ β q)
       where
       uniq : {m n : ℕ} {u v : ℕcode m n} → u ≡ v
       uniq {zero} {zero} {u} {v} = uniq𝟙 u ▪ uniq𝟙 v ⁻¹
       uniq {zero} {succ n} {()}
       uniq {succ m} {zero} {()}
       uniq {succ m} {succ n} {u} {v} = uniq {m = m}

-- Example 3.1.5
×isSet : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
       → {AisSet : isSet A} {BisSet : isSet B} → isSet (A × B)
×isSet {ℓ} {ℓ'} {A} {B} {AisSet} {BisSet} {x} {y} p q with ×≃ {A = A} {B = B} {x = x} {y = y}
×isSet {ℓ} {ℓ'} {A} {B} {AisSet} {BisSet} {x} {y} p q | mkisequiv g α h β =
       p ≡⟨ β p ⁻¹ ⟩
       h (ap pr₁ p , ap pr₂ p) ≡⟨ ap h (pair×≡ ( (AisSet (ap pr₁ p) (ap pr₁ q))
                                               , (BisSet (ap pr₂ p) (ap pr₂ q)))) ⟩
       h (ap pr₁ q , ap pr₂ q) ≡⟨ β q ⟩
       q ∎

-- Example 3.1.6
ΠisSet : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {BxisSet : (x : A) → isSet (B x)}
       → isSet ((x : A) → B x)
ΠisSet {ℓ} {ℓ'} {A} {B} {BxisSet} {f} {g} p q with (isequiv→qinv (funextentionality {f = f} {g = g}))
ΠisSet {ℓ} {ℓ'} {A} {B} {BxisSet} {f} {g} p q | mkqinv happly⁻¹ α β =
       p ≡⟨ β p ⁻¹ ⟩
       happly⁻¹ (λ x → happly p x) ≡⟨ ap happly⁻¹ (funext (λ x → BxisSet x (happly p x) (happly q x))) ⟩
       happly⁻¹ (λ x → happly q x) ≡⟨ β q ⟩
       q ∎

-- Definition 3.1.7
1-type : ∀ {ℓ} (A : Set ℓ) → Set _
1-type A = {x y : A} {p q : x ≡ y} (r s : p ≡ q) → r ≡ s

-- Lemma 3.1.8
isSet→1-type : ∀ {ℓ} {A : Set ℓ} → isSet A → 1-type A
isSet→1-type AisSet {x} {y} {p} {q} r s =
             h r ▪ h s ⁻¹
             where
             g : (p' : x ≡ y) → p ≡ p'
             g p' = AisSet p p'
             
             h : (r : p ≡ q) → r ≡ g p ⁻¹ ▪ (g q)
             h r =  r
                 ≡⟨ unit-left r ⟩
                    refl p ▪ r
                 ≡⟨ ap (λ p₁ → p₁ ▪ r) (p⁻¹▪p≡refly (g p) ⁻¹) ⟩
                    (g p ⁻¹ ▪ g p) ▪ r
                 ≡⟨ assoc▪ (g p ⁻¹) (g p) r ⁻¹ ⟩
                    g p ⁻¹ ▪ (g p ▪ r)
                 ≡⟨ ap (λ p₁ → g p ⁻¹ ▪ p₁) (transport[x↦a≡x] p r (g p) ⁻¹) ⟩
                    g p ⁻¹ ▪ ((r *) (g p))
                 ≡⟨ ap (λ p₁ → g p ⁻¹ ▪ p₁) (apd g r) ⟩
                    g p ⁻¹ ▪ (g q) ∎

-- Example 3.1.9
¬UisSet : ¬ (isSet Set)
¬UisSet UisSet = 0₂≠1₂ (ap (λ f → f 0₂) (f≡id ⁻¹))
                 where
                 f : 𝟚 → 𝟚
                 f 0₂ = 1₂
                 f 1₂ = 0₂                 

                 f≃ : isequiv f
                 f≃ = mkisequiv f (ind𝟚 (λ b → f (f b) ≡ b) (refl 0₂) (refl 1₂))
                                f (ind𝟚 (λ b → f (f b) ≡ b) (refl 0₂) (refl 1₂))                                

                 f̄≃≡id≃ : (f , f≃) ≡ (idtoeqv (refl 𝟚))
                 f̄≃≡id≃ with isequiv→qinv (univalence {A = 𝟚} {B = 𝟚})
                 f̄≃≡id≃ | mkqinv idtoeqv⁻¹ α β =
                        (f , f≃) ≡⟨ α (f , f≃) ⁻¹ ⟩
                        (idtoeqv (idtoeqv⁻¹ (f , f≃))) ≡⟨ ap idtoeqv (UisSet (idtoeqv⁻¹ (f , f≃))
                                                                             (idtoeqv⁻¹ (idtoeqv (refl 𝟚)))) ⟩
                        (idtoeqv (idtoeqv⁻¹ (idtoeqv (refl 𝟚)))) ≡⟨ α (idtoeqv (refl 𝟚)) ⟩
                        idtoeqv (refl 𝟚) ∎

                 f≡id : f ≡ id
                 f≡id = ap pr₁ f̄≃≡id≃
