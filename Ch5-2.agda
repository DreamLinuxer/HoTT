{-# OPTIONS --without-K #-}
module Ch5-2 where
open import Base
open import Ch5-1

data ℕ' : Set where
  0' : ℕ'
  succ' : ℕ' → ℕ'

recℕ' : ∀ {ℓ} (C : Set ℓ) → C → (ℕ' → C → C) → ℕ' → C
recℕ' C c₀ cs 0' = c₀
recℕ' C c₀ cs (succ' n) = cs n (recℕ' C c₀ cs n)

indℕ' : ∀ {ℓ} (C : ℕ' → Set ℓ) → C 0' → ((n : ℕ') → C n → C (succ' n)) → (n : ℕ') → C n
indℕ' C c₀ cs 0' = c₀
indℕ' C c₀ cs (succ' n) = cs n (indℕ' C c₀ cs n)

double : ℕ → ℕ
double = recℕ ℕ 0 (λ n m → succ (succ m))

double' : ℕ' → ℕ'
double' = recℕ' ℕ' 0' (λ n m → succ' (succ' m))

f : ℕ → ℕ'
f = recℕ ℕ' 0' (λ n → succ')

g : ℕ' → ℕ
g = recℕ' ℕ 0 (λ n → succ)

ε : g ∘ f ~ id
ε n = ap (λ f₁ → f₁ n) (uniq[ΠℕE] (g ∘ f) id 0 (λ _ → succ) (refl _) (refl _) (λ n → refl _) (λ n → refl _))

uniq[Πℕ'E] : ∀ {ℓ} {E : ℕ' → Set ℓ} (f g : (x : ℕ') → E x)
           → (ez : E 0') (es : (n : ℕ') → E n → E (succ' n))
           → f 0' ≡ ez → g 0' ≡ ez
           → ((n : ℕ') → f (succ' n) ≡ es n (f n))
           → ((n : ℕ') → g (succ' n) ≡ es n (g n))
           → f ≡ g
uniq[Πℕ'E] f g ez es f0 g0 fs gs =
           funext (indℕ' (λ x → f x ≡ g x) (f0 ▪ g0 ⁻¹) (λ n p → fs n ▪ ap (es n) p ▪ gs n ⁻¹))

η : f ∘ g ~ id
η n = ap (λ f₁ → f₁ n) (uniq[Πℕ'E] (f ∘ g) id 0' (λ _ → succ') (refl _) (refl _) (λ n → refl _) (λ n → refl _))

ℕ≃ℕ' : ℕ ≃ ℕ'
ℕ≃ℕ' = f , qinv→isequiv (g , η , ε)

double'' : ℕ' → ℕ'
double'' = λ n → f (double (g n))

data List𝟙 : Set where
  nil : List𝟙
  cons : 𝟙 × List𝟙 → List𝟙

indList𝟙 : ∀ {ℓ} (E : List𝟙 → Set ℓ) → E nil → ((u : 𝟙) → (l : List𝟙) → E l → E (cons (u , l))) → (l : List𝟙) → E l
indList𝟙 E enil econs nil = enil
indList𝟙 E enil econs (cons (u , l)) = econs u l (indList𝟙 E enil econs l)

0'' : List𝟙
0'' = nil

succ'' : List𝟙 → List𝟙
succ'' l = cons (⋆ , l)

indList𝟙' : ∀ {ℓ} (E : List𝟙 → Set ℓ) → E 0'' → ((l : List𝟙) → E l → E (succ'' l)) → (l : List𝟙) → E l
indList𝟙' E e0 es nil = e0
indList𝟙' E e0 es (cons (⋆ , l)) = es l (indList𝟙' E e0 es l)
