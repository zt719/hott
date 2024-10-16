module 02-Dependent-Function-Types where

open import 01-Prelude public

-- 2.1 Depedent function types
Π : (A : UU ℓ₁) (B : A → UU ℓ₂) → UU (ℓ₁ ⊔ ℓ₂)
Π A B = (x : A) → B x
syntax Π A (λ x → b) = Π[ x ∈ A ] b

indΠ : {A : UU ℓ₁} {P : A → UU ℓ₂}
  → ((x : A) → P x)
  → Π[ x ∈ A ] P x
indΠ f = λ x → f x

-- 2.2 Ordinary function types
_⇒_ : UU ℓ₁ → UU ℓ₂ → UU (ℓ₁ ⊔ ℓ₂)
A ⇒ B = Π[ x ∈ A ] B
infixr 0 _⇒_

id : {A : UU ℓ₁}
  → A → A
id x = x

comp : {A : UU ℓ₁} {B : UU ℓ₂} {C : UU ℓ₃}
  → (B → C) → (A → B) → (A → C)
comp g f x = g (f x)

_∘_ = comp
infixr 9 _∘_

-- 2.3 Exercises

const : {A : UU ℓ₁} {B : UU ℓ₂}
  → B → A → B
const y _ = y

swap : {A : UU ℓ₁} {B : UU ℓ₂}
  → {P : A → B → UU ℓ₃}
  → ((x : A) (y : B) → P x y)
  → (y : B) (x : A) → P x y
swap f x y = f y x

σ = swap
