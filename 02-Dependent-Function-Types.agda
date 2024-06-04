module 02-Dependent-Function-Types where

open import 01-Prelude public

-- 2.1 Depedent function types
private Π : (A : UU i) (B : A → UU j) → UU (i ⊔ j)
Π A B = (x : A) → B x
syntax Π A (λ x → b) = Π x ∶ A , b

indΠ : {A : UU i} {P : A → UU j}
  → ((x : A) → P x)
  → Π x ∶ A , P x
indΠ f = λ x → f x

-- 2.2 Ordinary function types
private _⇒_ : UU i → UU j → UU (i ⊔ j)
A ⇒ B = Π x ∶ A , B
infixr  0 _⇒_

id : (A : UU i)
  → A → A
id A x = x

comp : {A : UU i} {B : UU j} {C : UU k}
  → (B → C) → (A → B) → (A → C)
comp g f x = g (f x)

_∘_ = comp
infixr 9 _∘_

-- 2.3 Exercises

const : {A : UU i} {B : UU j}
  → B → A → B
const y _ = y

swap : {A : UU i} {B : UU j} {C : A → B → UU k}
  → ((x : A) (y : B) → C x y)
  → (y : B) (x : A) → C x y
swap f x y = f y x

σ = swap
