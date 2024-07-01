module 11-Fundamental-Theorem where

open import 10-Contractible-Types public

-- 11.1 Families of equivalences

tot : {A : UU l₁} {B : A → UU l₂} {C : A → UU l₃}
  → ((x : A) → B x → C x)
  → Σ x ∶ A , B x → Σ x ∶ A , C x
tot f (x , y) = x , f x y

lem11-1-2 : {A : UU l₁} {B : A → UU l₂} {C : A → UU l₃}
  → (f : (x : A) → B x → C x)
  → (t : Σ x ∶ A , C x)
  → fib (tot f) t ≃ fib (f (pr₁ t)) (pr₂ t)
lem11-1-2 {A = A} {B} {C} f t = {!!}
  where
    φ : (t : Σ x ∶ A , C x) → fib (tot f) t → fib (f (pr₁ t)) (pr₂ t)
    φ (x , .(f x y)) ((.x , y) , refl .(x , f x y)) = y , refl (f x y)

    ψ : (t : Σ x ∶ A , C x) → fib (f (pr₁ t)) (pr₂ t) → fib (tot f) t
    ψ (x , .(f x y)) (y , refl .(f x y)) = (x , y) , refl (x , f x y)

