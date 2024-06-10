module 02-Dependent-Function-Types where

open import 01-Prelude public

-- 2.1 Depedent function types
Π : (A : UU l₁) (B : A → UU l₂) → UU (l₁ ⊔ l₂)
Π A B = (x : A) → B x
syntax Π A (λ x → b) = Π x ∶ A , b

indΠ : {A : UU l₁} {P : A → UU l₂}
  → ((x : A) → P x)
  → Π x ∶ A , P x
indΠ f = λ x → f x

-- 2.2 Ordinary function types
_⇒_ : UU l₁ → UU l₂ → UU (l₁ ⊔ l₂)
A ⇒ B = Π x ∶ A , B
infixr 0 _⇒_

id : {A : UU l₁}
  → A → A
id x = x

comp : {A : UU l₁} {B : UU l₂} {C : UU l₃}
  → (B → C) → (A → B) → (A → C)
comp g f x = g (f x)

_∘_ = comp
infixr 9 _∘_

-- 2.3 Exercises

const : {A : UU l₁} {B : UU l₂}
  → B → A → B
const y _ = y

swap : {A : UU l₁} {B : UU l₂}
  → {P : A → B → UU l₃}
  → ((x : A) (y : B) → P x y)
  → (y : B) (x : A) → P x y
swap f x y = f y x

σ = swap
