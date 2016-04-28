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
  encode∘decode~id {zeroℕ} {zeroℕ} c = uniq𝟙 c ⁻¹
  encode∘decode~id {succ m} {zeroℕ} c = rec𝟘 (encode (succ m) zeroℕ (rec𝟘 (succ m ≡ zeroℕ) c) ≡ c) c
  encode∘decode~id {zeroℕ} {succ n} c = rec𝟘 (encode zeroℕ (succ n) (rec𝟘 (zeroℕ ≡ succ n) c) ≡ c) c
  encode∘decode~id {succ m} {succ n} c =  encode (succ m) (succ n) (ap succ (decode m n c))
                                       ≡⟨ refl _ ⟩
                                          transport (λ n → code (succ m) n) (ap succ (decode m n c)) (r (succ m))
                                       ≡⟨ transport[P∘f,p,u]≡transport[P,ap[f,p],u] succ ((λ n → code (succ m) n)) (decode m n c) (r m) ⁻¹ ⟩
                                          transport (λ n → code (succ m) (succ n)) (decode m n c) (r m)
                                       ≡⟨ refl _ ⟩
                                          transport (λ n → code m n) (decode m n c) (r m)
                                       ≡⟨ refl _ ⟩
                                          encode m n (decode m n c)
                                       ≡⟨ encode∘decode~id {m = m} {n = n} c ⟩
                                          c ∎
--2.13.2
succ[m]≠zeroℕ : {m : ℕ} → succ m ≡ zeroℕ → 𝟘
succ[m]≠zeroℕ {m} = Natural.encode (succ m) zeroℕ
