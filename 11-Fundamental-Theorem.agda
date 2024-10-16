module 11-Fundamental-Theorem where

open import 10-Contractible-Types public

Eq⊎ : {A : UU ℓ₁} {B : UU ℓ₂}
  → (EqA : A → A → UU)
  → (EqB : B → B → UU)
  → A ⊎ B → A ⊎ B → UU
Eq⊎ EqA EqB (inl x) (inl x₁) = EqA x x₁
Eq⊎ EqA EqB (inl x) (inr y₁) = 𝟘
Eq⊎ EqA EqB (inr y) (inl x₁) = 𝟘
Eq⊎ EqA EqB (inr y) (inr y₁) = EqB y y₁

-- 11.1 Families of equivalences

tot : {A : UU ℓ₁} {B : A → UU ℓ₂} {C : A → UU ℓ₃}
  → ((x : A) → B x → C x)
  → Σ[ x ∈ A ] B x → Σ[ x ∈ A ] C x
tot f (x , y) = x , f x y

{-
lem11-1-2 : {A : UU ℓ₁} {B : A → UU ℓ₂} {C : A → UU ℓ₃}
  → (f : (x : A) → B x → C x)
  → (t : Σ[ x ∈ A ] C x)
  → fib (tot f) t ≃ fib (f (pr₁ t)) (pr₂ t)
lem11-1-2 {A = A} {B} {C} f t = (φ t) , ((ψ t , {!!}) , ({!!} , {!!}))
  where
    φ : (t : Σ[ x ∈ A ] C x) → fib (tot f) t → fib (f (pr₁ t)) (pr₂ t)
    φ (x , .(f x y)) ((.x , y) , refl .(x , f x y)) = y , refl (f x y)

    ψ : (t : Σ[ x ∈ A ] C x) → fib (f (pr₁ t)) (pr₂ t) → fib (tot f) t
    ψ (x , .(f x y)) (y , refl .(f x y)) = (x , y) , refl (x , f x y)

    G : (t : Σ[ x ∈ A ] C x) → φ t ∘ ψ t ~ id
    G (x , pr₄) = {!!}
-}
