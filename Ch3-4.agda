module Ch3-4 where
open import Base
open import Ch3-3

--3.4.1
LEM : ∀ {ℓ} → Set _
LEM {ℓ} = (A : Set ℓ) → isProp A → A + (¬ A)

--3.4.2
doubleneg : ∀ {ℓ} → Set _
doubleneg {ℓ} = (A : Set ℓ) → isProp A → (¬ ¬ A → A)

LEM∞ : ∀ {ℓ} → Set _
LEM∞ {ℓ} = (A : Set ℓ) → A + (¬ A)

--Definition 3.4.3
decidable : ∀ {ℓ} → (A : Set ℓ) → Set _
decidable A = A + (¬ A)

decidableF : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') → Set _
decidableF {A = A} B = (a : A) → B a + (¬ B a)

decidableEQ : ∀ {ℓ} → (A : Set ℓ) → Set _
decidableEQ A = (a b : A) → (a ≡ b) + (¬ (a ≡ b))
