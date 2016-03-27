{-# OPTIONS --without-K #-}

module Ch2-9 where
open import Ch2-8 public

--2.9
happly : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
         f ≡ g → ((x : A) → f x ≡ g x)
happly {ℓ} {ℓ'} {A} {B} {f} {g} p =
       ind≡ (λ f g p → (x : A) → f x ≡ g x)
            (λ f x → refl (f x))
            f g p

--Axiom 2.9.3
postulate
  funextentionality : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
                      isequiv (happly {f = f} {g = g})

funext : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
         ((x : A) → f x ≡ g x) → f ≡ g
funext {ℓ} {ℓ'} {A} {B} {f} {g} with (isequiv→qinv (funextentionality {f = f} {g = g}))
funext | happly⁻¹ , (α , β) = happly⁻¹

computationΠ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
               (h : (x : A) → f x ≡ g x) → (x : A) → happly (funext h) x ≡ h x
computationΠ {ℓ} {ℓ'} {A} {B} {f} {g} h x with (isequiv→qinv (funextentionality {f = f} {g = g}))
computationΠ h x | happly⁻¹ , (α , β) = ap (λ f → f x) (α h)

uniqΠ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
        (p : f ≡ g) → p ≡ funext (λ x → happly p x)
uniqΠ {ℓ} {ℓ'} {A} {B} {f} {g} p with (isequiv→qinv (funextentionality {f = f} {g = g}))
uniqΠ p | happly⁻¹ , (α , β)= β p ⁻¹

refΠ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (f : (x : A) → B x) →
       refl f ≡ funext (λ x → refl (f x))
refΠ f = refl f
       ≡⟨ uniqΠ (refl f) ⟩
         funext (happly (refl f))
       ≡⟨ ap funext (refl (λ x → refl (f x))) ⟩
         funext (λ x → refl (f x)) ∎

Π⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
      (α : f ≡ g) → α ⁻¹ ≡ funext (λ x → (happly α x) ⁻¹)
Π⁻¹ {ℓ} {ℓ'} {A} {B} {f} {g} α =
    ind≡ (λ f g α → α ⁻¹ ≡ funext (λ x → happly α x ⁻¹))
         (λ f → refl f ⁻¹
              ≡⟨ uniqΠ (refl f ⁻¹) ⟩
                funext (λ x → happly (refl f ⁻¹) x)
              ≡⟨ ap funext (refl (λ x → refl (f x))) ⟩
                funext (λ x → happly (refl f) x ⁻¹) ∎)
         f g α

▪Π : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g h : (x : A) → B x} →
     (α : f ≡ g) (β : g ≡ h) → α ▪ β ≡ funext (λ x → happly α x ▪ happly β x)
▪Π {ℓ} {ℓ'} {A} {B} {f} {g} {h} α β =
   ind≡ (λ f g α → (h : (x : A) → B x) → (β : g ≡ h)
                 → α ▪ β ≡ funext (λ x → happly α x ▪ happly β x))
        (λ f h β →
           ind≡ (λ f h β → refl f ▪ β ≡ funext (λ x → happly (refl f) x ▪ happly β x))
                (λ f → refl f ▪ refl f
                     ≡⟨ uniqΠ (refl f ▪ refl f) ⟩
                       funext (λ x → happly (refl f ▪ refl f) x)
                     ≡⟨ ap funext (refl (λ x → refl (f x))) ⟩
                       funext (λ x → happly (refl f) x ▪ happly (refl f) x) ∎)
                f h β)
        f g α h β

transport→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} {x₁ x₂ : X} →
             (p : x₁ ≡ x₂) (f : A x₁ → B x₁) → transport (λ x → A x → B x) p f ≡ (λ x → transport B p (f (transport A (p ⁻¹) x)))
transport→ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x₁} {x₂} p f =
           ind≡ (λ x₁ x₂ p → (f : A x₁ → B x₁)
                           → transport (λ x → A x → B x) p f ≡ (λ x → transport B p (f (transport A (p ⁻¹) x))))
                (λ x f → refl f)
                x₁ x₂ p f

Π : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} (A : X → Set ℓ') (B : (x : X) → A x → Set ℓ'') → X → Set (ℓ'' ⊔ ℓ')
Π A B = (λ x → (a : A x) → B x a)

B^ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : (x : X) → A x → Set ℓ''} → Σ[ x ∈ X ] (A x) → Set ℓ''
B^ {B = B} = (λ w → B (pr₁ w) (pr₂ w))

transportΠ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : (x : X) → A x → Set ℓ''} {x₁ x₂ : X} →
             (p : x₁ ≡ x₂) (f : (a : A x₁) → B x₁ a) (a : A x₂) →
             transport (Π A B) p f a
             ≡
             transport (B^ {B = B}) ((pairΣ≡ {w = x₂ , a} {w' = x₁ , ((p ⁻¹) *) a} (p ⁻¹ , refl (((p ⁻¹) *) a))) ⁻¹)  (f (transport A (p ⁻¹) a))
transportΠ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x₁} {x₂} p f a =
           ind≡ (λ x₁ x₂ p → (f : (a : A x₁) → B x₁ a) (a : A x₂)
                           → transport (Π A B) p f a
                           ≡ transport (B^ {B = B}) ((pairΣ≡ {w = x₂ , a} {w' = x₁ , ((p ⁻¹) *) a} (p ⁻¹ , refl (((p ⁻¹) *) a))) ⁻¹)  (f (transport A (p ⁻¹) a)))
                (λ x f a → refl (f a))
                x₁ x₂ p f a

--Lemma 2.9.6
eq→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} {x y : X} →
      (p : x ≡ y) (f : A x → B x) (g : A y → B y) →
      ((p *) f ≡ g) ≃ ((a : A x) → (p *) (f a) ≡ g ((p *) a))
eq→ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {y} p f g =
    ind≡ (λ x y p → (f : A x → B x) (g : A y → B y)
                  → ((p *) f ≡ g) ≃ ((a : A x) → (p *) (f a) ≡ g ((p *) a)))
         (λ x f g → happly , funextentionality)
         x y p f g
^→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} {x y : X} →
     {p : x ≡ y} {f : A x → B x} {g : A y → B y} → (q : (p *) f ≡ g) →
     ((a : A x) → (p *) (f a) ≡ g ((p *) a))
^→ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {y} {p} {f} {g} with eq→ p f g
^→ | happly , _ = happly

path→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} {x y : X} →
        {p : x ≡ y} {f : A x → B x} {g : A y → B y} {q : (p *) f ≡ g} (a : A x) →
        (_* {P = λ x → A x → B x} p f) ((p *) a) ≡ g ((p *) a)
path→ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {y} {p} {f} {g} {q} a =
      (_* {P = λ x → A x → B x} p f) ((p *) a)
   ≡⟨ ap (λ h → h ((p *) a)) (transport→ p f) ⟩
      (p *) (f ((_* {P = A} (p ⁻¹)) ((p *) a)))
   ≡⟨ ap (λ z → (p *) (f z)) (q*[p*[u]]≡[[p▪q]*][u] A p (p ⁻¹) a) ⟩
      (p *) (f (_* {P = A} (p ▪ p ⁻¹) a))
   ≡⟨ ap (λ r → (p *) (f (_* {P = A} r a))) (p▪p⁻¹≡reflx p) ⟩
      (p *) (f a)
   ≡⟨ ^→ {p = p} q a ⟩
      g ((p *) a) ∎

eq→₁ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} {x y : X} →
       {p : x ≡ y} {f : A x → B x} {g : A y → B y} {q : (p *) f ≡ g} (a : A x) →
       happly q ((p *) a) ≡ path→ {p = p} {q = q} a
eq→₁ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {y} {p} {f} {g} {q} a =
     ind≡ (λ x y p → (f : A x → B x) → (g : A y → B y) → (q : (p *) f ≡ g)
                   → (a : A x) → happly q ((p *) a) ≡ path→ {p = p} {q = q} a)
          (λ x f g q a →
             ind≡ (λ f g q → (a : A x) → happly q (_* {P = A} (refl x) a) ≡ path→ {A = A} {B = B} {p = refl x} {q = q} a)
                  (λ f a → refl (refl (f a)))
                  (_* {P = λ x → A x → B x} (refl x) f) g q a)
          x y p f g q a

--Lemma 2.9.7
eqΠ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : (x : X) → A x → Set ℓ''} {x y : X} →
      (p : x ≡ y) (f : (a : A x) → B x a) (g : (a : A y) → B y a) →
      ((p *) f ≡ g) ≃ ((a : A x) → transport (B^ {B = B}) (pairΣ≡ {w = x , a} {w' = y , (p *) a} (p , refl ((p *) a))) (f a) ≡ g ((p *) a))
eqΠ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {y} p f g =
    ind≡ (λ x y p → (f : (a : A x) → B x a) → (g : (a : A y) → B y a)
                  → ((p *) f ≡ g)
                  ≃ ((a : A x) → transport (B^ {B = B}) (pairΣ≡ {w = x , a} {w' = y , (p *) a} (p , refl ((p *) a))) (f a) ≡ g ((p *) a)))
         (λ x f g → happly , funextentionality)
         x y p f g

eqΠ→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : (x : X) → A x → Set ℓ''} {x y : X} →
      {p : x ≡ y} {f : (a : A x) → B x a} {g : (a : A y) → B y a} →
      ((p *) f ≡ g) → ((a : A x) → transport (B^ {B = B}) (pairΣ≡ {w = x , a} {w' = y , (p *) a} (p , refl ((p *) a))) (f a) ≡ g ((p *) a))
eqΠ→ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {y} {p} {f} {g} with eqΠ p f g
eqΠ→ | 𝒇 , _ = 𝒇

eqΠ← : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : (x : X) → A x → Set ℓ''} {x y : X} →
      {p : x ≡ y} {f : (a : A x) → B x a} {g : (a : A y) → B y a} →
      ((a : A x) → transport (B^ {B = B}) (pairΣ≡ {w = x , a} {w' = y , (p *) a} (p , refl ((p *) a))) (f a) ≡ g ((p *) a)) → ((p *) f ≡ g)
eqΠ← {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {y} {p} {f} {g} with eqΠ p f g
eqΠ← | 𝒇 , iseq with isequiv→qinv iseq
eqΠ← | 𝒇 , iseq | 𝒇⁻¹ , (α , β) = 𝒇⁻¹

compΠ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : (x : X) → A x → Set ℓ''} {x y : X} →
        (p : x ≡ y) (f : (a : A x) → B x a) (g : (a : A y) → B y a) →
        (h : (a : A x) → transport (B^ {B = B}) (pairΣ≡ {w = x , a} {w' = y , (p *) a} (p , refl ((p *) a))) (f a) ≡ g ((p *) a)) →
        (a : A x) → eqΠ→ {p = p} {f = f} {g = g} (eqΠ← {p = p} {f = f} {g = g} h) a ≡ h a
compΠ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {y} p f g h a with eqΠ p f g
compΠ p f g h a | 𝒇 , iseq with isequiv→qinv iseq
compΠ p f g h a | 𝒇 , iseq | 𝒇⁻¹ , (α , β) = ap (λ f → f a) (α h)
