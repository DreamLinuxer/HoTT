{-# OPTIONS --without-K #-}
module Ch5-5 where
open import Base
open import Level
open import Ch3
open import Ch5-4

module _ where
  open import Ch5-3
  indℕᵂ : ∀ {ℓ} (E : ℕᵂ → Set ℓ) (ez : E 0ᵂ) (es : (n : ℕᵂ) → E n → E (succᵂ n))
          → (n : ℕᵂ) → E n
  indℕᵂ E ez es (sup 0₂ f) = transport E (ap (sup 0₂) (funext (λ ()))) ez
  indℕᵂ E ez es (sup 1₂ f) = transport E (ap (sup 1₂) (funext λ {⋆ → refl _}))
                                       (es (f ⋆) (indℕᵂ E ez es (f ⋆)))

Wd : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂) → Set _
Wd {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B =
   Σ[ W ∈ Set ℓ₃ ] Σ[ sup ∈ ((a : A) → ((B a → W) → W)) ]
   ((E : W → Set ℓ₄) → ((e : (a : A) (f : B a → W) → ((b : B a) → E (f b)) → E (sup a f)) →
                        Σ[ ind ∈ ((w : W) → E w) ] ((a : A) (f : B a → W) → (ind (sup a f)) ≡ e a f (λ b → ind (f b)))))

-- Theorem 5.5.1
postulate
  WdisProp : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂) → isProp (Wd {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B)

Wₛ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂) → Set _
Wₛ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B =
   Σ[ W ∈ Set ℓ₃ ] Σ[ sup ∈ ((a : A) → ((B a → W) → W)) ]
   ((C : Set ℓ₄) (c : ((a : A) → (B a → C) → C)) →
    Σ[ rec ∈ (W → C) ] Σ[ β ∈ ((a : A) (f : B a → W) → rec (sup a f) ≡ c a (λ b → rec (f b))) ]
    ((g : W → C) (h : W → C)
     (βg : ((a : A) (f : B a → W) → g (sup a f) ≡ c a (λ b → g (f b))))
     (βh : ((a : A) (f : B a → W) → h (sup a f) ≡ c a (λ b → h (f b)))) →
     Σ[ α ∈ ((w : W) → g w ≡ h w) ] ( (a : A) (f : B a → W)
                                    → α (sup a f) ▪ βh a f ≡ βg a f ▪ ap (c a) (funext λ b → α (f b)))))

-- Theorem 5.5.1
postulate
  WₛisProp : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂) → isProp (Wₛ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B)

Wₕ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂) → Set _
Wₕ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B = Σ[ I ∈ WAlg {A = A} {B = B} {ℓ = ℓ₃} ] isHinitW {ℓ' = ℓ₄} I

-- Theorem 5.5.3
postulate
  WₕisProp : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂) → isProp (Wₕ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B)

-- Lemma 5.5.4
postulate
  Wd≃Wₛ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂)
        → Wd {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B ≃ Wₛ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B
  Wₛ≃Wₕ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂)
        → Wₛ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B ≃ Wₕ {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} A B

-- Theorem 5.5.5
module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Set ℓ₁) (B : A → Set ℓ₂)
         (𝑾 : WAlg {A = A} {B = B} {ℓ₃})
         (𝑾isHinit : isHinitW {ℓ' = ℓ₃ ⊔ ℓ₄} 𝑾)
         (𝑾isHinit' : isHinitW {ℓ' = ℓ₃} 𝑾) where
  W = pr₁ 𝑾
  sw = pr₂ 𝑾

  W-intro : (a : A) (t : B a → W) → W
  W-intro a t = sw a t

  W-elim×W-comp : (C' : W → Set ℓ₄)
                → (c' : (a : A) (t : B a → W) (g : (b : B a) → C' (t b)) → C' (sw a t))
                → Σ[ rec ∈ ((w : W) → C' w) ] ((a : A) (t : B a → W) → rec (sw a t) ≡ c' a t (λ b → rec (t b)))
  W-elim×W-comp C' c' = rec , Wcomp
    where
    C = Σ[ w ∈ W ] C' w
    sc : (a : A) → (B a → C) → C
    sc a t = (sw a (pr₁ ∘ t)) , c' a (pr₁ ∘ t) (λ b → pr₂ (t b))
    
    𝑪 : WAlg {A = A} {B = B}
    𝑪 = C , sc

    𝑭 : WHom 𝑾 𝑪
    𝑭 = pr₁ (𝑾isHinit 𝑪)
    f = pr₁ 𝑭
    sf = pr₂ 𝑭

    𝑮 : WHom 𝑪 𝑾
    𝑮 = pr₁ , λ a t → refl (sw a (pr₁ ∘ t))
    g = pr₁ 𝑮
    sg = pr₂ 𝑮

    𝑮∘𝑭 : WHom 𝑾 𝑾
    𝑮∘𝑭 = g ∘ f , λ a t → ap g (sf a t)
    g∘f = pr₁ 𝑮∘𝑭
    sg∘f = pr₂ 𝑮∘𝑭

    𝒊𝒅 : WHom 𝑾 𝑾
    𝒊𝒅 = id , λ a t → refl _
    sid = pr₂ 𝒊𝒅

    𝒑 : 𝑮∘𝑭 ≡ 𝒊𝒅
    𝒑 = (pr₂ (𝑾isHinit' 𝑾) 𝑮∘𝑭) ⁻¹ ▪ (pr₂ (𝑾isHinit' 𝑾) 𝒊𝒅)

    p : pr₁ ∘ f ≡ id
    p = pr₁ (pairΣ≡⁻¹ 𝒑)

    rec : (w : W) → C' w
    rec w = transport C' (happly p w) (pr₂ (f w))

    lem₁ : (a : A) (t : B a → W) → happly p (sw a t) ≡ sg∘f a t ▪ ap (sw a) (funext λ b → happly p (t b))
    lem₁ a t = unit-right (happly p (sw a t)) ▪ (nat a t 𝑮∘𝑭 𝒊𝒅 𝒑) ⁻¹
      where
      nat : (a : A) (t : B a → W) → (𝒇 𝒈 : WHom 𝑾 𝑾) → (𝒑 : 𝒇 ≡ 𝒈)
          → (pr₂ 𝒇) a t ▪ ap (sw a) (funext λ b → happly (pr₁ (pairΣ≡⁻¹ 𝒑)) (t b))
          ≡ happly (pr₁ (pairΣ≡⁻¹ 𝒑)) (sw a t) ▪ (pr₂ 𝒈) a t
      nat a t (f , sf) (.f , .sf) (refl .(f , sf)) = ap (λ p → sf a t ▪ ap (sw a) p) (refΠ _)⁻¹
                                                   ▪ (unit-right (sf a t) ⁻¹
                                                   ▪ unit-left _)

    lem₂ : (a : A) (t : B a → W) → transport C' (sg∘f a t) (pr₂ (f (sw a t)))
                                 ≡ c' a (g∘f ∘ t) (λ b → pr₂ (f (t b)))
    lem₂ a t = ap (λ p → transport C' p (pr₂ (f (sw a t)))) q
             ▪ pr₂ (pairΣ≡⁻¹ (sf a t))
      where
      q : sg∘f a t ≡ pr₁ (pairΣ≡⁻¹ (sf a t))
      q = pairΣ≡₁' (sf a t)
      
    lem₃ : (a : A) (t : B a → W) → transport C' (ap (sw a) (funext λ b → happly p (t b))) (c' a (g∘f ∘ t) (λ b → pr₂ (f (t b))))
                                 ≡ c' a t (λ b → rec (t b))
    lem₃ a t = lem a {t₁ = g∘f ∘ t} {t₂ = t} ((funext λ b → happly p (t b))) (λ b → pr₂ (f (t b)))
             ▪ ap (λ h → c' a t (λ b → transport C' (h b) (pr₂ (f (t b))))) (compΠ≡ (λ b → happly p (t b)))
      where
      lem : (a : A) {t₁ t₂ : B a → W} (p : t₁ ≡ t₂) (v : (b : B a) → C' (t₁ b))
          → transport C' (ap (sw a) p) (c' a t₁ v) ≡ c' a t₂ (λ b → transport C' (happly p b) (v b))
      lem a (refl t) v = refl _

    Wcomp : (a : A) (t : B a → W) → rec (sw a t) ≡ c' a t (λ b → rec (t b))
    Wcomp a t = transport C' (happly p (sw a t)) (pr₂ (f (sw a t)))
             ≡⟨ ap (λ p₁ → transport C' p₁ (pr₂ (f (sw a t)))) (lem₁ a t) ⟩
                transport C' (sg∘f a t ▪ ap (sw a) (funext λ b → happly p (t b)))
                             (pr₂ (f (sw a t)))
             ≡⟨ transport▪ C' (sg∘f a t) _ (pr₂ (f (sw a t))) ⁻¹ ⟩
                transport C' (ap (sw a) (funext λ b → happly p (t b)))
                             (transport C' (sg∘f a t) (pr₂ (f (sw a t))))
             ≡⟨ ap (transport C' (ap (sw a) (funext (λ b → happly p (t b))))) (lem₂ a t) ⟩
                transport C' (ap (sw a) (funext λ b → happly p (t b))) (c' a (g∘f ∘ t) (λ b → pr₂ (f (t b))))
             ≡⟨ lem₃ a t ⟩
                c' a t (λ b → rec (t b)) ∎
