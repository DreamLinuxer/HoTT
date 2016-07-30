{-# OPTIONS --without-K #-}

module Base where
open import Ch1 public
import Level

infixr 20 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (g : B → C) → (f : A → B) → (A → C)
_∘_ g f = (λ x → g (f x))

--Lemma 2.1.1
infix 21 _⁻¹
_⁻¹ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
refl x ⁻¹ = refl x

--Lemma 2.1.2
infixl 10 _▪_
_▪_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl x ▪ refl .x = refl x 

--Lemma 2.1.4
unit-right : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ≡ p ▪ (refl y)
unit-right (refl x) = refl (refl x)

unit-left : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ≡ (refl x) ▪ p
unit-left (refl x) = refl (refl x)

p⁻¹▪p≡refly : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⁻¹ ▪ p ≡ refl y
p⁻¹▪p≡refly (refl x) = refl (refl x)

p▪p⁻¹≡reflx : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ▪ p ⁻¹ ≡ refl x
p▪p⁻¹≡reflx (refl x) = refl (refl x)

p⁻¹⁻¹≡p : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
p⁻¹⁻¹≡p (refl x) = refl (refl x)

assoc▪ : ∀ {ℓ} {A : Set ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ▪ (q ▪ r) ≡ (p ▪ q) ▪ r
assoc▪ (refl x) (refl .x) (refl .x) = refl (refl x)

infixr 1 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ α ⟩ β = α ▪ β

infix 2 _∎
_∎ : ∀ {ℓ} {A : Set ℓ} (p : A) → p ≡ p
p ∎ = refl p

--Lemma 2.2.1
ap : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

--Lemma 2.2.2
ap▪ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (x y z : A) →
      (p : x ≡ y) → (q : y ≡ z) →
      ap f (p ▪ q) ≡ ap f p ▪ ap f q
ap▪ f x .x .x (refl .x) (refl .x) = refl (refl (f x))

ap⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (x y : A) →
       (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
ap⁻¹ f x .x (refl .x) = refl (refl (f x))

ap∘ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
      (f : A → B) (g : B → C) (x y : A) → (p : x ≡ y) →
      ap g (ap f p) ≡ ap (g ∘ f) p
ap∘ f g x .x (refl .x) = refl (refl (g (f x)))

apid : ∀ {ℓ} {A : Set ℓ} (x y : A) → (p : x ≡ y) →
       ap id p ≡ p
apid x .x (refl .x) = refl (refl x)

--Lemma 2.3.1
transport : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (p : x ≡ y) → P x → P y
transport P (refl x) p = p

_* : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} (p : x ≡ y) → P x → P y
_* {P = P} p = transport P p 

--Lemma 2.3.2
lift : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y : A} (u : P x) (p : x ≡ y) → (x , u) ≡ (y , (_* {P = P} p) u)
lift P u (refl x) = refl (x , u)

--Lemma 2.3.4
apd : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f : (x : A) → P x)
      {x y : A} (p : x ≡ y) → (p *) (f x) ≡ f y
apd f (refl x) = refl (f x)

--Lemma 2.3.5
transportconst : ∀ {ℓ} {ℓ'} {A : Set ℓ} (B : Set ℓ') {x y : A} (p : x ≡ y) →
                 (b : B) → transport (λ x → B) p b ≡ b
transportconst {ℓ} {ℓ'} {A} B {x} {.x} (refl .x) b = refl b

--Lemma 2.3.8
apd≡transportconst▪ap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) {x y : A} (p : x ≡ y) →
                        apd f p ≡ transportconst B p (f x) ▪ ap f p
apd≡transportconst▪ap {ℓ} {ℓ'} {A} {B} f {x} {.x} (refl .x) = refl (refl (f x))

--Lemma 2.3.9
q*[p*[u]]≡[[p▪q]*][u] : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y z : A} (p : x ≡ y) (q : y ≡ z) →
                        (u : P x) → (q *) (_* {P = P} p u) ≡ ((p ▪ q) *) u
q*[p*[u]]≡[[p▪q]*][u] {ℓ} {ℓ'} {A} P {x} {.x} {.x} (refl .x) (refl .x) u = refl u

--Lemma 2.3.10
transport[P∘f,p,u]≡transport[P,ap[f,p],u] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (P : B → Set ℓ'')
                                            {x y : A} (p : x ≡ y) (u : P (f x)) →
                                            transport (P ∘ f) p u ≡ transport P (ap f p) u
transport[P∘f,p,u]≡transport[P,ap[f,p],u] {ℓ} {ℓ'} {A} {B} f P {x} {.x} (refl .x) u = refl u

--Lemma 2.3.11
transport[Q,p,f[x,u]]≡f[y,transport[P,p,u]] : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} (P : A → Set ℓ') (Q : A → Set ℓ'') →
                                              (f : (x : A) → P x → Q x) →
                                              {x y : A} (p : x ≡ y) (u : P x) →
                                              transport Q p (f x u) ≡ f y (transport P p u)
transport[Q,p,f[x,u]]≡f[y,transport[P,p,u]] {ℓ} {ℓ'} {ℓ''} {A} P Q f {x} {.x} (refl .x) u = refl (f x u)

infix 2 _~_

_~_ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} (f g : (x : A) → P x) → Set (ℓ ⊔ ℓ')
_~_ {A = A} f g = (x : A) → f x ≡ g x

--Lemma 2.4.2
ref~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → f ~ f
ref~ f = λ x → refl (f x)

sym~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g : A → B} → f ~ g → g ~ f
sym~ {ℓ} {ℓ'} {A} {B} {f} {g} f~g = λ x → (f~g x) ⁻¹

tran~ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f g h : A → B} → f ~ g → g ~ h → f ~ h
tran~ {ℓ} {ℓ'} {A} {B} {f} {g} {h} f~g g~h = λ x → (f~g x) ▪ (g~h x)


--Lemma 2.4.3
ntran~ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f g : A → B) (H : f ~ g) {x y : A} (p : x ≡ y) →
         H x ▪ ap g p ≡ ap f p ▪ H y
ntran~ f g H (refl x) = (unit-right (H x))⁻¹ ▪ unit-left (H x)

--Corollary 2.4.4
comm~' : ∀ {ℓ} {A : Set ℓ} (f : A → A) (H : f ~ id) (x : A) →
         H (f x) ▪ H x ≡ ap f (H x) ▪ H x
comm~' {ℓ} {A} f H x = (H (f x) ▪ H x)
                     ≡⟨ ap (λ p → H (f x) ▪ p) (apid (f x) x (H x) ⁻¹) ⟩
                       H (f x) ▪ ap id (H x)
                     ≡⟨ ntran~ f id H (H x) ⟩
                       (ap f (H x) ▪ H x ∎)

comm~ : ∀ {ℓ} {A : Set ℓ} (f : A → A) (H : f ~ id) (x : A) →
        H (f x) ≡ ap f (H x)
comm~ {ℓ} {A} f H x = H (f x)
                    ≡⟨ unit-right (H (f x)) ⟩
                      H (f x) ▪ refl (f x)
                    ≡⟨ ap (λ p → H (f x) ▪ p) (p▪p⁻¹≡reflx (H x)) ⁻¹ ⟩
                      H (f x) ▪ (H x ▪ H x ⁻¹)
                    ≡⟨ assoc▪ (H (f x)) (H x) (H x ⁻¹)⟩
                      H (f x) ▪ H x ▪ H x ⁻¹
                    ≡⟨ ap (λ p → p ▪ H x ⁻¹) (comm~' f H x) ⟩
                      ap f (H x) ▪ H x ▪ H x ⁻¹
                    ≡⟨ assoc▪ (ap f (H x)) (H x) (H x ⁻¹) ⁻¹ ⟩
                      ap f (H x) ▪ (H x ▪ H x ⁻¹)
                    ≡⟨ ap (λ p → ap f (H x) ▪ p) (p▪p⁻¹≡reflx (H x)) ⟩
                      ap f (H x) ▪ refl (f x)
                    ≡⟨ unit-right (ap f (H x)) ⁻¹ ⟩
                      ap f (H x) ∎

--Definition 2.4.6
qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
qinv {ℓ} {ℓ'} {A} {B} f = Σ[ g ∈ (B → A) ] (f ∘ g ~ id) × (g ∘ f ~ id)

isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
isequiv {ℓ} {ℓ'} {A} {B} f = (Σ[ g ∈ (B → A) ] (f ∘ g ~ id) ) × (Σ[ h ∈ (B → A) ] (h ∘ f ~ id) )

qinv→isequiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               qinv f → isequiv f
qinv→isequiv (g , α , β) = (g , α) , (g , β)

isequiv→qinv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} →
               isequiv f → qinv f
isequiv→qinv {f = f} ((g , α) , (h , β)) =
             let γ : g ~ h
                 γ x = (β (g x) ⁻¹) ▪ (ap h (α x))
             in  g , (α , (λ x → (γ (f x)) ▪ (β x)))

infix 2 _≃_
_≃_ : ∀ {ℓ} {ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isequiv f)

--Lemma 2.4.12
ref≃ : ∀ {ℓ} {A : Set ℓ} → A ≃ A
ref≃ = id , ((id , refl) , (id , refl))

sym≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → B ≃ A
sym≃ (f , eq) with (isequiv→qinv eq)
sym≃ (f , eq) | (f⁻¹ , (α , β)) = f⁻¹ , ((f , β) , (f , α))

tran≃ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
        A ≃ B → B ≃ C → A ≃ C
tran≃ (f , eq1) (g , eq2) with (isequiv→qinv eq1)
tran≃ (f , eq1) (g , eq2) | (f⁻¹ , (α1 , β1)) with (isequiv→qinv eq2)
tran≃ (f , eq1) (g , eq2) | (f⁻¹ , (α1 , β1)) | (g⁻¹ , (α2 , β2)) =
      (g ∘ f) , ((f⁻¹ ∘ g⁻¹ , (λ x → g (f (f⁻¹ (g⁻¹ x)))
                                   ≡⟨ ap (λ y → g y) (α1 (g⁻¹ x)) ⟩
                                     g (g⁻¹ x)
                                   ≡⟨ α2 x ⟩
                                     x ∎))
              ,  (f⁻¹ ∘ g⁻¹ , (λ x → f⁻¹ (g⁻¹ (g (f x)))
                                   ≡⟨ ap (λ y → f⁻¹ y) (β2 (f x)) ⟩
                                     f⁻¹ (f x)
                                   ≡⟨ β1 x ⟩
                                     x ∎)))


infix 3 _○_
_○_ : ∀ {ℓ} {ℓ'} {ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} →
      (f : B ≃ C) (g : A ≃ B) → A ≃ C
g ○ f  = tran≃ f g

infix 20 _⁻¹≃
_⁻¹≃ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A ≃ B) → B ≃ A
_⁻¹≃ f = sym≃ f

--2.6
pair×≡⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B} →
           (x ≡ y) → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)
pair×≡⁻¹ p = (ap pr₁ p) , (ap pr₂ p)

pair×≡' : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a a' : A} {b b' : B} →
          (a ≡ a') × (b ≡ b') → (a , b) ≡ (a' , b')
pair×≡' {ℓ} {ℓ'} {A} {B} {a} {.a} {b} {.b} (refl .a , refl .b) = refl (a , b)

pair×≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B}
       → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y) → (x ≡ y)
pair×≡ {ℓ} {ℓ'} {A} {B} {a , b} {a' , b'} = pair×≡' {ℓ} {ℓ'} {A} {B} {a} {a'} {b} {b'}

--Theorem 2.6.2
pair×≡⁻¹∘pair×≡~id : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B}
                   → (pair×≡⁻¹ {A = A} {B = B} {x = x} {y = y}) ∘ pair×≡ ~ id
pair×≡⁻¹∘pair×≡~id {x = x₁ , x₂}{y = .x₁ , .x₂} (refl .x₁ , refl .x₂) = refl (refl x₁ , refl x₂)

pair×≡∘pair×≡⁻¹~id : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B}
                   → (pair×≡ {A = A} {B = B} {x = x} {y = y}) ∘ pair×≡⁻¹ ~ id
pair×≡∘pair×≡⁻¹~id {y = y₁ , y₂} (refl .(y₁ , y₂)) = refl (refl (y₁ , y₂))

×≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A × B}
   → isequiv (pair×≡⁻¹ {ℓ} {ℓ'} {A} {B} {x} {y})
×≃ {ℓ} {ℓ'} {A} {B} {x} {y} = qinv→isequiv (pair×≡ , pair×≡⁻¹∘pair×≡~id , pair×≡∘pair×≡⁻¹~id)

uniq×₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (z : A × B) → ((pr₁ z , pr₂ z) ≡ z)
uniq×₁ z = pair×≡ ((refl (pr₁ z)) , (refl (pr₂ z)))

--Theorem 2.6.4
transport× : ∀ {ℓ ℓ' ℓ''} {Z : Set ℓ} {A : Z → Set ℓ'} {B : Z → Set ℓ''}
             {z w : Z} (p : z ≡ w) (x : A z × B z) →
             transport (λ z → A z × B z) p x ≡ (transport (λ z → A z) p (pr₁ x) , transport (λ z → B z) p (pr₂ x))
transport× {ℓ} {ℓ'} {ℓ''} {Z} {A} {B} {z} {.z} (refl .z) x = (uniq×₁ x) ⁻¹

--Theorem 2.6.5
ap× : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} {A' : Set ℓ₃} {B' : Set ℓ₄} →
      (g : A → A') (h : B → B') (x y : A × B) (p : pr₁ x ≡ pr₁ y) (q : pr₂ x ≡ pr₂ y) →
      (ap (λ x → (g (pr₁ x) , h (pr₂ x))) (pair×≡ {x = x} {y = y} (p , q))) ≡ (pair×≡ (ap g p , ap h q))
ap× {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄} {A} {B} {A'} {B'} g h (a , b) (.a , .b) (refl .a) (refl .b) = refl (refl (g a , h b))

--2.7
--Theorem 2.7.2
Σ≃ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
     (w ≡ w') ≃ (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
Σ≃ {ℓ} {ℓ'} {A} {P} {w} {w'} =
   f , qinv→isequiv (g , f∘g~id {w} {w'} , g∘f~id)
   where f : {w w' : Σ[ x ∈ A ] P x} → (w ≡ w') → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
         f {w} {.w} (refl .w) = refl (pr₁ w) , refl (pr₂ w)
         
         g : {w w' : Σ[ x ∈ A ] P x} → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))) → w ≡ w'
         g {w₁ , w₂} {.w₁ , .w₂} (refl .w₁ , refl .w₂) = refl (w₁ , w₂)
                          
         f∘g~id : {w w' : Σ[ x ∈ A ] P x} → (f {w} {w'}) ∘ g ~ id
         f∘g~id {w₁ , w₂} {.w₁ , .w₂} (refl .w₁ , refl .w₂) = refl (refl w₁ , refl w₂)

         g∘f~id : {w w' : Σ[ x ∈ A ] P x} → (g {w} {w'}) ∘ f ~ id
         g∘f~id {w₁ , w₂} {.w₁ , .w₂} (refl .(w₁ , w₂)) = refl (refl (w₁ , w₂))

--Corollary 2.7.3
uniqΣ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} → (z : Σ[ x ∈ A ] P x) → z ≡ (pr₁ z , pr₂ z)
uniqΣ {ℓ} {ℓ'} {A} {P} z with Σ≃ {w = z} {w' = (pr₁ z , pr₂ z)}
uniqΣ z | f , ((g , α) , (h , β)) = g (refl (pr₁ z) , refl (pr₂ z))

pairΣ≡⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
           (w ≡ w') → (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w')))
pairΣ≡⁻¹ {w = w} {w' = w'} with Σ≃ {w = w} {w' = w'}
pairΣ≡⁻¹ | f , ((g , α) , (h , β)) = f

pairΣ≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {w w' : Σ[ x ∈ A ] P x} →
         (Σ[ p ∈ (pr₁ w ≡ pr₁ w') ] ((_* {P = P} p) (pr₂ w) ≡ (pr₂ w'))) → w ≡ w'
pairΣ≡ {w = w} {w' = w'} with Σ≃ {w = w} {w' = w'}
pairΣ≡ | f , ((g , α) , (h , β)) = g

--Theorem 2.7.4
liftΣ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {P : A → Set ℓ'} {Q : (Σ[ x ∈ A ] (P x)) → Set ℓ''} →
        {x y : A} (p : x ≡ y) (u : P x) (z : Q (x , u)) →
        _* {P = λ x → Σ[ u ∈ (P x) ] (Q (x , u))} p (u , z)
        ≡
        ((p *) u , _* {P = Q} (pairΣ≡ (p , refl ((p *) u))) z)
liftΣ {ℓ} {ℓ'} {ℓ''} {A} {P} {Q} {x} {.x} (refl .x) u z = refl (u , z)

--2.8
𝟙≡⁻¹ : {x y : 𝟙} → (x ≡ y) → 𝟙
𝟙≡⁻¹ _ = ⊤

𝟙≡ : {x y : 𝟙} → 𝟙 → (x ≡ y)
𝟙≡ {⊤} {⊤} ⊤ = refl ⊤

--Theorem 2.8.1
𝟙≃ : {x y : 𝟙} → (x ≡ y) ≃ 𝟙
𝟙≃ {x} {y} = 𝟙≡⁻¹ , qinv→isequiv (𝟙≡ , (λ { ⊤ → refl ⊤ })
                                     , (ind≡ (λ x y p → (𝟙≡ ∘ 𝟙≡⁻¹) p ≡ p)
                                             (λ {⊤ → refl (refl ⊤)})
                                             x y))

uniq𝟙 : (u : 𝟙) → u ≡ ⊤
uniq𝟙 ⊤ = refl ⊤

--2.9

happly : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
         f ≡ g → ((x : A) → f x ≡ g x)
happly {ℓ} {ℓ'} {A} {B} {f} {.f} (refl .f) x = refl (f x)

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
computationΠ h x | happly⁻¹ , α , β = ap (λ f → f x) (α h)

uniqΠ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
        (p : f ≡ g) → p ≡ funext (λ x → happly p x)
uniqΠ {ℓ} {ℓ'} {A} {B} {f} {g} p with (isequiv→qinv (funextentionality {f = f} {g = g}))
uniqΠ p | happly⁻¹ , α , β = β p ⁻¹

refΠ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (f : (x : A) → B x) →
       refl f ≡ funext (λ x → refl (f x))
refΠ f = refl f
       ≡⟨ uniqΠ (refl f) ⟩
         funext (happly (refl f))
       ≡⟨ ap funext (refl (λ x → refl (f x))) ⟩
         funext (λ x → refl (f x)) ∎

Π⁻¹ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
      (α : f ≡ g) → α ⁻¹ ≡ funext (λ x → (happly α x) ⁻¹)
Π⁻¹ {ℓ} {ℓ'} {A} {B} {f} {.f} (refl .f) = refl f ⁻¹
                                       ≡⟨ uniqΠ (refl f ⁻¹) ⟩
                                          funext (λ x → happly (refl f ⁻¹) x)
                                       ≡⟨ ap funext (refl (λ x → refl (f x))) ⟩
                                          funext (λ x → happly (refl f) x ⁻¹) ∎

▪Π : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g h : (x : A) → B x} →
     (α : f ≡ g) (β : g ≡ h) → α ▪ β ≡ funext (λ x → happly α x ▪ happly β x)
▪Π {ℓ} {ℓ'} {A} {B} {f} {.f} {.f} (refl .f) (refl .f) = refl f ▪ refl f
                                                     ≡⟨ uniqΠ (refl f ▪ refl f) ⟩
                                                        funext (λ x → happly (refl f ▪ refl f) x)
                                                     ≡⟨ ap funext (refl (λ x → refl (f x))) ⟩
                                                        funext (λ x → happly (refl f) x ▪ happly (refl f) x) ∎

-- 2.9.4
transport→ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : X → Set ℓ''} {x₁ x₂ : X}
           → (p : x₁ ≡ x₂) (f : A x₁ → B x₁)
           → transport (λ x → A x → B x) p f ≡ (λ x → transport B p (f (transport A (p ⁻¹) x)))
transport→ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {.x} (refl .x) f = refl f

Π : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} (A : X → Set ℓ') (B : (x : X) → A x → Set ℓ'') → X → Set (ℓ'' ⊔ ℓ')
Π A B = (λ x → (a : A x) → B x a)

B^ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : (x : X) → A x → Set ℓ''} → Σ[ x ∈ X ] (A x) → Set ℓ''
B^ {B = B} = (λ w → B (pr₁ w) (pr₂ w))

transportΠ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : (x : X) → A x → Set ℓ''} {x₁ x₂ : X} →
             (p : x₁ ≡ x₂) (f : (a : A x₁) → B x₁ a) (a : A x₂) →
             transport (Π A B) p f a
             ≡
             transport (B^ {B = B}) ((pairΣ≡ {w = x₂ , a} {w' = x₁ , ((p ⁻¹) *) a} (p ⁻¹ , refl (((p ⁻¹) *) a))) ⁻¹)  (f (transport A (p ⁻¹) a))
transportΠ {ℓ} {ℓ'} {ℓ''} {X} {A} {B} {x} {.x} (refl .x) f a = refl (f a)

--2.10
--Lemma 2.10.1
idtoeqv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
idtoeqv {ℓ} {A} {B} p = (p *) , ind≡ (λ A B p → isequiv (p *))
                                     (λ A → qinv→isequiv (id , refl , refl))
                                     A B p

--Axiom 2.10.3
postulate
  univalence : ∀ {ℓ} {A B : Set ℓ} → isequiv (idtoeqv {A = A} {B = B})

ua : ∀ {ℓ} {A B : Set ℓ} → (A ≃ B) → (A ≡ B)
ua {ℓ} {A} {B} with isequiv→qinv (univalence {A = A} {B = B})
ua | idtoeqv⁻¹ , α , β = idtoeqv⁻¹

elim≡ : ∀ {ℓ} {A B : Set ℓ} → pr₁ ∘ (idtoeqv {A = A} {B = B}) ≡ transport (λ x → x)
elim≡ {ℓ} {A} {B} = funext (λ p → refl (p *))

computation≡ : ∀ {ℓ} {A B : Set ℓ} (f : A ≃ B) (x : A) → transport (λ x → x) (ua f) x ≡ (pr₁ f) x
computation≡ {ℓ} {A} {B} f x with isequiv→qinv (univalence {A = A} {B = B})
computation≡ {A = A} {B = B} f x | idtoeqv⁻¹ , (α , β) = transport (λ x → x) (idtoeqv⁻¹ f) x
                                                      ≡⟨ refl ((idtoeqv⁻¹ f *) x) ⟩
                                                         (pr₁ (idtoeqv {A = A} {B = B} (idtoeqv⁻¹ f))) x
                                                      ≡⟨ ap (λ eq → (pr₁ eq) x) (α f) ⟩
                                                         pr₁ f x ∎

uniq≡ : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) → p ≡ ua (idtoeqv p)
uniq≡ {ℓ} {A} {B} p with isequiv→qinv (univalence {A = A} {B = B})
uniq≡ p | idtoeqv⁻¹ , (α , β) = (β p) ⁻¹

comp≡ : ∀ {ℓ} {A B : Set ℓ} (eq : A ≃ B) → eq ≡ idtoeqv (ua eq)
comp≡ {ℓ} {A} {B} eq with isequiv→qinv (univalence {A = A} {B = B})
comp≡ eq | idtoeqv⁻¹ , (α , β) = (α eq) ⁻¹

ref≡ : ∀ {ℓ} {A : Set ℓ} → refl A ≡ ua ref≃
ref≡ {ℓ} {A} with isequiv→qinv (univalence {A = A} {B = A})
ref≡ {ℓ} {A} | idtoeqv⁻¹ , (α , β) = refl A
                                   ≡⟨ β (refl A) ⁻¹ ⟩
                                     idtoeqv⁻¹ (idtoeqv (refl A))
                                   ≡⟨ ap idtoeqv⁻¹ (refl ref≃) ⟩
                                     (idtoeqv⁻¹ ref≃) ∎

▪≡' : ∀ {ℓ} {A B C : Set ℓ} (p : A ≡ B) (q : B ≡ C) → (idtoeqv (p ▪ q)) ≡ (idtoeqv q ○ idtoeqv p)
▪≡' {ℓ} {A} {B} {C} p q = ind≡ (λ A B p → (C : Set ℓ) → (q : B ≡ C)
                                        → (idtoeqv (p ▪ q)) ≡ (idtoeqv q ○ idtoeqv p))
                               (λ A C q → ind≡ (λ A C q → (idtoeqv ((refl A) ▪ q)) ≡ (idtoeqv q ○ idtoeqv (refl A)))
                                               (λ A → refl (idtoeqv (refl A)))
                                               A C q)
                               A B p C q

▪≡ : ∀ {ℓ} {A B C : Set ℓ} (f : A ≃ B) (g : B ≃ C) → (ua f) ▪ (ua g) ≡ ua (g ○ f)
▪≡ {ℓ} {A} {B} {C} f g =
      ua f ▪ ua g
   ≡⟨ uniq≡ (ua f ▪ ua g) ⟩
      ua (idtoeqv (ua f ▪ ua g))
   ≡⟨ ap ua (▪≡' (ua f) (ua g)) ⟩
      ua (idtoeqv (ua g) ○ idtoeqv (ua f))
   ≡⟨ ap (λ r → ua (r ○ idtoeqv (ua f))) ((comp≡ g) ⁻¹) ⟩
      ua (g ○ idtoeqv (ua f))
   ≡⟨ ap (λ r → ua (g ○ r)) (comp≡ f ⁻¹) ⟩
      ua (g ○ f) ∎

≡⁻¹' : ∀ {ℓ} {A B : Set ℓ} (p : A ≡ B) → idtoeqv (p ⁻¹) ≡ (idtoeqv p) ⁻¹≃
≡⁻¹' {ℓ} {A} {B} p = ind≡ (λ A B p → idtoeqv (p ⁻¹) ≡ (idtoeqv p) ⁻¹≃)
                          (λ A → refl (idtoeqv (refl A)))
                          A B p

≡⁻¹ : ∀ {ℓ} {A B : Set ℓ} (f : A ≃ B) → (ua f) ⁻¹ ≡ ua (f ⁻¹≃)
≡⁻¹ {ℓ} {A} {B} f =  (ua f ⁻¹)
                  ≡⟨ uniq≡ ((ua f) ⁻¹) ⟩
                     ua (idtoeqv ((ua f) ⁻¹))
                  ≡⟨ ap (λ p → ua p) (≡⁻¹' (ua f)) ⟩
                     ua ((idtoeqv (ua f)) ⁻¹≃)
                  ≡⟨ ap (λ p → ua (p ⁻¹≃)) ((comp≡ f) ⁻¹) ⟩
                     ua (f ⁻¹≃) ∎

--Lemma 2.10.5
transport≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {x y : A} →
             (p : x ≡ y) (u : B x) → transport B p u ≡ (pr₁ (idtoeqv (ap B p))) u
transport≡ {ℓ} {ℓ'} {A} {B} {x} {y} p u =
           transport ((λ x → x) ∘ B) p u
        ≡⟨ transport[P∘f,p,u]≡transport[P,ap[f,p],u] B (λ x₁ → x₁) p u ⟩
           transport (λ x → x) (ap B p) u
        ≡⟨ ap (λ f → (f (ap B p)) u) elim≡ ⟩
           (pr₁ (idtoeqv (ap B p))) u ∎

--2.11

--Lemma 2.11.2
transport[x↦a≡x] : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ : A} (a : A) (p : x₁ ≡ x₂) (q : a ≡ x₁) →
                   transport (λ x → a ≡ x) p q ≡ q ▪ p
transport[x↦a≡x] {ℓ} {A} {x} {.x} a (refl .x) q = unit-right q

transport[x↦x≡a] : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ : A} (a : A) (p : x₁ ≡ x₂) (q : x₁ ≡ a) →
                   transport (λ x → x ≡ a) p q ≡ p ⁻¹ ▪ q
transport[x↦x≡a] {ℓ} {A} {x} {.x} a (refl .x) q = unit-left q

transport[x↦x≡x] : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ : A} (a : A) (p : x₁ ≡ x₂) (q : x₁ ≡ x₁) →
                   transport (λ x → x ≡ x) p q ≡ p ⁻¹ ▪ q ▪ p
transport[x↦x≡x] {ℓ} {A} {x} {.x} a (refl .x) q = (unit-left q) ▪ unit-right (refl x ⁻¹ ▪ q)

--2.12
+code : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} → A + B → Set _
+code {a₀ = a₀} (inl a) = a₀ ≡ a
+code {a₀ = a₀} (inr b) = Level.Lift 𝟘

--Theorem 2.12.5
+encode : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (p : inl a₀ ≡ x)
        → +code {a₀ = a₀} x
+encode {ℓ} {ℓ'} {A} {B} {a₀} x p = transport +code p (refl a₀)

+decode : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (c : +code {a₀ = a₀} x)
        → inl a₀ ≡ x
+decode {a₀ = a₀} (inl a) c = ap inl c
+decode {a₀ = a₀} (inr b) c = rec𝟘 (inl a₀ ≡ inr b) (Level.lower c)

+decode∘+encode~id : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (p : inl a₀ ≡ x)
                 → +decode x (+encode x p) ≡ p
+decode∘+encode~id {A = A} {a₀ = a₀} x p =
                   ind≡' (inl a₀) (λ x₁ p₁ → +decode x₁ (+encode x₁ p₁) ≡ p₁)
                         (refl (refl (inl a₀))) x p

+encode∘+decode~id : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) (c : +code {a₀ = a₀} x)
                 → +encode x (+decode x c) ≡ c
+encode∘+decode~id (inl a₀) (refl .a₀) = refl (refl a₀)
+encode∘+decode~id (inr b) (Level.lift ())

≃+ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₀ : A} (x : A + B) → (inl a₀) ≡ x ≃ +code x
≃+ {a₀ = a₀} x = (+encode x) , qinv→isequiv ((+decode x) , (+encode∘+decode~id x) , (+decode∘+encode~id x))

𝟚≃𝟙+𝟙 : 𝟚 ≃ 𝟙 + 𝟙
𝟚≃𝟙+𝟙 = (λ { 0₂ → inl ⊤ ; 1₂ → inr ⊤ })
      , qinv→isequiv ( (λ {(inl ⊤) → 0₂ ; (inr ⊤) → 1₂})
                     , (λ {(inl ⊤) → refl (inl ⊤) ; (inr ⊤) → refl (inr ⊤)})
                     , (λ { 0₂ → refl 0₂ ; 1₂ → refl 1₂ }))

0₂≠1₂ : 0₂ ≠ 1₂
0₂≠1₂ eq = Level.lower (+encode (inr ⊤) (ap (λ { 0₂ → inl ⊤ ; 1₂ → inr ⊤ }) eq))

--2.13

ℕcode : ℕ → ℕ → Set
ℕcode zeroℕ zeroℕ = 𝟙
ℕcode (succ m) zeroℕ = 𝟘
ℕcode zeroℕ (succ n) = 𝟘
ℕcode (succ m) (succ n) = ℕcode m n

ℕr : (n : ℕ) → ℕcode n n
ℕr zeroℕ = ⊤
ℕr (succ n) = ℕr n

--Theorem 2.13.1
ℕencode : {m n : ℕ} → m ≡ n → ℕcode m n
ℕencode {m} {n} p = transport (λ n → ℕcode m n) p (ℕr m)

ℕdecode : {m n : ℕ} → ℕcode m n → m ≡ n
ℕdecode {zeroℕ} {zeroℕ} x = refl zeroℕ
ℕdecode {succ m} {zeroℕ} x = rec𝟘 (succ m ≡ zeroℕ) x
ℕdecode {zeroℕ} {succ n} x = rec𝟘 (zeroℕ ≡ succ n) x
ℕdecode {succ m} {succ n} x = ap succ (ℕdecode x)

ℕdecode∘ℕencode~id : {m n : ℕ} → (p : m ≡ n) → ℕdecode (ℕencode p) ≡ p
ℕdecode∘ℕencode~id {zeroℕ} (refl .zeroℕ) = refl (refl zeroℕ)
ℕdecode∘ℕencode~id {succ m} (refl .(succ m)) = ap (λ x → ap succ x) (ℕdecode∘ℕencode~id (refl m))

ℕencode∘ℕdecode~id : {m n : ℕ} → (c : ℕcode m n) → ℕencode (ℕdecode {m = m} c) ≡ c
ℕencode∘ℕdecode~id {zeroℕ} {zeroℕ} ⊤ = refl ⊤
ℕencode∘ℕdecode~id {zeroℕ} {succ n} ()
ℕencode∘ℕdecode~id {succ m} {zeroℕ} ()
ℕencode∘ℕdecode~id {succ m} {succ n} c =  transport (ℕcode (succ m)) (ap succ (ℕdecode c)) (ℕr m)
                                       ≡⟨ transport[P∘f,p,u]≡transport[P,ap[f,p],u] succ (ℕcode (succ m)) (ℕdecode c) (ℕr m) ⁻¹ ⟩
                                          transport (ℕcode (succ m) ∘ succ) (ℕdecode c) (ℕr m)
                                       ≡⟨ ℕencode∘ℕdecode~id {m = m} c ⟩
                                          c ∎

ℕ≃ : {m n : ℕ} → (m ≡ n) ≃ ℕcode m n
ℕ≃ {m} {n} = ℕencode
           , qinv→isequiv ( ℕdecode
                          , (ℕencode∘ℕdecode~id {m = m})
                          , ℕdecode∘ℕencode~id)
