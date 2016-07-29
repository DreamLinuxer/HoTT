module Ch3-1 where
open import Base

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
