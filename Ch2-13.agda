{-# OPTIONS --without-K #-}

module Ch2-13 where
open import Ch2-12 public

module Natural where
  code : ℕ → ℕ → Set
  code zeroℕ zeroℕ = 𝟙
  code (succ m) zeroℕ = 𝟘
  code zeroℕ (succ n) = 𝟘
  code (succ m) (succ n) = code m n

  r : (n : ℕ) → code n n
  r zeroℕ = ⊤
  r (succ n) = r n

--Theorem 2.13.1
  encode : (m n : ℕ) → m ≡ n → code m n
  encode m n p = transport (λ n → code m n) p (r m)

  decode : (m n : ℕ) → code m n → m ≡ n
  decode zeroℕ zeroℕ x = refl zeroℕ
  decode (succ m) zeroℕ x = rec𝟘 (succ m ≡ zeroℕ) x
  decode zeroℕ (succ n) x = rec𝟘 (zeroℕ ≡ succ n) x
  decode (succ m) (succ n) x = ap succ (decode m n x)

  decode∘encode~id : {m n : ℕ} → (p : m ≡ n) → decode m n (encode m n p) ≡ p
  decode∘encode~id {m} {n} p = ind≡ (λ m n p → decode m n (encode m n p) ≡ p)
                                    (indℕ (λ n → decode n n (r n) ≡ refl n)
                                          (refl (refl zeroℕ))
                                          (λ n p →  ap succ (decode n n (r n))
                                                 ≡⟨ ap (λ x → ap succ x) p ⟩
                                                    ap succ (refl n)
                                                 ≡⟨ refl (refl (succ n)) ⟩
                                                    refl (succ n) ∎))
                                    m n p

  encode∘decode~id : {m n : ℕ} → (c : code m n) → encode m n (decode m n c) ≡ c
  encode∘decode~id {m} {n} c = {!!}
