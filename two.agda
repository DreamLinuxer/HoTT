{-# OPTIONS --without-K #-}

module two where
open import Base
open import Uni-fib
open import Ch3
open import Ex2
open import Ex3
open Ex2-13
open Ex3-1

𝟚₀ : BAut 𝟚
𝟚₀ = 𝟚 , ∣ refl _ ∣

`id `not : 𝟚₀ ≡ 𝟚₀
`id = refl _
`not = pairΣ≡ (ua not≃ , inhabPath _ _)

¬id=not : ¬ (`id ≡ `not)
¬id=not id=not = rec𝟘 _ (not≃≠ref≃ not≃≡ref≃)
  where
  0≠1 : ¬ (0₂ ≡ 1₂)
  0≠1 ()

  not≃≠ref≃ : ¬ (not≃ ≡ ref≃)
  not≃≠ref≃ not≡ref = rec𝟘 _ (0≠1 (ap (λ eq → ≃→ eq 0₂) not≡ref ⁻¹))

  not≃≡ref≃ : not≃ ≡ ref≃
  not≃≡ref≃ = comp≡ not≃
            ▪ ap idtoeqv (pairΣ≡₁ (ua not≃ , inhabPath _ _) ⁻¹)
            ▪ ap (λ x → idtoeqv (ap pr₁ x)) id=not ⁻¹

Ω𝟚₀≃𝟚 : Ω 𝟚₀ ≃ 𝟚
Ω𝟚₀≃𝟚 = ΩBAut≃Aut ▪≃ [𝟚≃𝟚]≃𝟚

lemma : ≃→ Ω𝟚₀≃𝟚 `not ≡ 1₂
lemma = lem (≃→ Ω𝟚₀≃𝟚 `not) (refl _)
  where
  lem : (b : 𝟚) → ≃→ Ω𝟚₀≃𝟚 `not ≡ b → ≃→ Ω𝟚₀≃𝟚 `not ≡ 1₂
  lem 0₂ r = rec𝟘 _ (¬id=not (≃η Ω𝟚₀≃𝟚 `id ⁻¹ ▪ ap (≃← Ω𝟚₀≃𝟚) r ⁻¹ ▪ ≃η Ω𝟚₀≃𝟚 `not))
  lem 1₂ r = r

all-1-path : (p : 𝟚₀ ≡ 𝟚₀) → (p ≡ `id) + (p ≡ `not)
all-1-path p = lem (≃→ Ω𝟚₀≃𝟚 p) (refl _)
  where
  lem : (b : 𝟚) → ≃→ Ω𝟚₀≃𝟚 p ≡ b → (p ≡ `id) + (p ≡ `not)
  lem 0₂ r = inl (≃η Ω𝟚₀≃𝟚 p ⁻¹ ▪ ap (≃← Ω𝟚₀≃𝟚) r ▪ ≃η Ω𝟚₀≃𝟚 `id )
  lem 1₂ r = inr (≃η Ω𝟚₀≃𝟚 p ⁻¹ ▪ ap (≃← Ω𝟚₀≃𝟚) r ▪ ap (≃← Ω𝟚₀≃𝟚) lemma ⁻¹ ▪ ≃η Ω𝟚₀≃𝟚 `not)

Ω𝟚₀isSet : isSet (Ω 𝟚₀)
Ω𝟚₀isSet = ≃isSet 𝟚isSet (Ω𝟚₀≃𝟚 ⁻¹≃)

all-2-path : (p : 𝟚₀ ≡ 𝟚₀) → (r : p ≡ p) → r ≡ refl p
all-2-path p r = Ω𝟚₀isSet _ _ _ _
