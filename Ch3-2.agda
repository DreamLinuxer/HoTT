module Ch3-2 where
open import Base

--Theorem 3.2.2
¬double-neg : ¬ ((A : Set) → ((¬ (¬ A)) → A))
¬double-neg f = ¬e[x]≡x (f 𝟚 u) eq
                where
                e : 𝟚 → 𝟚
                e 0₂ = 1₂
                e 1₂ = 0₂                 

                e≃ : isequiv e
                e≃ = (e , (ind𝟚 (λ b → e (e b) ≡ b) (refl 0₂) (refl 1₂)))
                   , (e , (ind𝟚 (λ b → e (e b) ≡ b) (refl 0₂) (refl 1₂)))

                p : 𝟚 ≡ 𝟚
                p = ua (e , e≃)

                u : ¬ ¬ 𝟚
                u x = x 0₂

                uniq¬¬𝟚 : {u v : ¬ ¬ 𝟚} → u ≡ v
                uniq¬¬𝟚 {u} {v} = funext (λ x → rec𝟘 (u x ≡ v x) (x 0₂))

                eq : e (f 𝟚 u) ≡ f 𝟚 u
                eq =  e (f 𝟚 u)
                   ≡⟨ computation≡ (e , e≃) (f 𝟚 u) ⁻¹ ⟩
                      transport (λ A → A) p (f 𝟚 u)
                   ≡⟨ ap (λ x → transport (λ A → A) p (f 𝟚 x)) uniq¬¬𝟚 ⟩
                      transport (λ A → A) p (f 𝟚 (transport (λ A → ¬ ¬ A) (p ⁻¹) u))
                   ≡⟨ ap (λ g → g u) (transport→ p (f 𝟚) ⁻¹) ⟩
                      transport (λ A → ¬ ¬ A → A) p (f 𝟚) u
                   ≡⟨ happly (apd f p) u ⟩
                      f 𝟚 u ∎

                ¬e[x]≡x : (x : 𝟚) → ¬ ((e x) ≡ x)
                ¬e[x]≡x 0₂ ()
                ¬e[x]≡x 1₂ ()

-- Corollary 3.2.7
¬LEM : ¬ ((A : Set) → (A + (¬ A)))
¬LEM g = ¬double-neg (λ A u → h (g A) u)
         where
         h : {A : Set} → A + (¬ A) → ¬ ¬ A → A
         h {A} (inl a) u = a
         h {A} (inr w) u = rec𝟘 A (u w)
