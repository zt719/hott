module 04-Inductive-Types where

open import 03-Natural-Numbers public

-- 4.2 The unit type
record 𝟙 : UU where
  constructor ＊
{-# BUILTIN UNIT 𝟙 #-}

ind𝟙 : {P : 𝟙 → UU ℓ₁}
  → P ＊ → (x : 𝟙) → P x
ind𝟙 p ＊ = p

-- 4.3 The empty type
data 𝟘 : UU where

ind𝟘 : {P : 𝟘 → UU ℓ₁}
  → (x : 𝟘) → P x
ind𝟘 = λ ()

ex-falso : {A : UU ℓ₁}
  → 𝟘 → A
ex-falso = ind𝟘

-- 4.3.2 Negation
¬_ : UU ℓ₁ → UU ℓ₁
¬ A = A → 𝟘

¬¬_ : UU ℓ₁ → UU ℓ₁
¬¬ A = ¬ A → 𝟘

is-empty : (A : UU ℓ₁) → UU ℓ₁ 
is-empty A = A → 𝟘

_~ : {P : UU ℓ₁} {Q : UU ℓ₂}
  → (P → Q)
  → ¬ Q → ¬ P
(f ~) q~ p = q~ (f p)

-- 4.4 Corpoducts

infixr 2 _⊎_
data _⊎_ (A : UU ℓ₁) (B : UU ℓ₂) : UU (ℓ₁ ⊔ ℓ₂) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

ind⊎ : {A : UU ℓ₁} {B : UU ℓ₂} {P : A ⊎ B → UU ℓ₃}
  → ((x : A) → P (inl x))
  → ((y : B) → P (inr y))
  → (z : A ⊎ B) → P z
ind⊎ f g (inl x) = f x

ind⊎ f g (inr y) = g y

[_,_] : {A : UU ℓ₁} {B : UU ℓ₂} {P : A ⊎ B → UU ℓ₃}
  → ((x : A) → P (inl x))
  → ((y : B) → P (inr y))
  → (z : A ⊎ B) → P z
[ f , g ] = ind⊎ f g

_⊎ᶠ_ : {A : UU ℓ₁} {A' : UU ℓ₂} {B : UU ℓ₃ } {B' : UU ℓ₄}
  → (f : A → A') (g : B → B') → A ⊎ B → A' ⊎ B'
(f ⊎ᶠ g) (inl x) = inl (f x)
(f ⊎ᶠ g) (inr y) = inr (g y)

-- 4.5 THe type of integers

ℤ = ℕ ⊎ (𝟙 ⊎ ℕ)

in-pos : ℕ → ℤ
in-pos = inr ∘ inr

in-neg : ℕ → ℤ
in-neg = inl

-1ℤ : ℤ
-1ℤ = in-neg zero

0ℤ : ℤ
0ℤ = inr (inl ＊)

1ℤ : ℤ
1ℤ = in-pos zero

indℤ : {P : ℤ → UU ℓ₁}
  → P -1ℤ
  → ((n : ℕ) → P (in-neg n) → P (in-neg (suc n)))
  → P 0ℤ
  → P 1ℤ
  → ((n : ℕ) → P (in-pos n) → P (in-pos (suc n)))
  → (k : ℤ) → P k
indℤ p-1 p-s p0 p1 ps (inl zero) = p-1
indℤ p-1 p-s p0 p1 ps (inl (suc n))
  = p-s n (indℕ p-1 p-s n)
indℤ p-1 p-s p0 p1 ps (inr (inl ＊)) = p0
indℤ p-1 p-s p0 p1 ps (inr (inr zero)) = p1
indℤ p-1 p-s p0 p1 ps (inr (inr (suc n)))
  = ps n (indℕ p1 ps n)

succℤ : ℤ → ℤ
succℤ (inl zero) = 0ℤ
succℤ (inl (suc n)) = in-neg n
succℤ (inr (inl ＊)) = 1ℤ
succℤ (inr (inr n)) = in-pos (suc n)

-- 4.6 Dependent pair types
infixr 4 _,_
record Σ (A : UU ℓ₁) (B : A → UU ℓ₂) : UU (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁
open Σ public
{-# BUILTIN SIGMA Σ #-}

Σ-syntax : (A : UU ℓ₁) (B : A → UU ℓ₂) → UU (ℓ₁ ⊔ ℓ₂)
Σ-syntax = Σ

infix 2 Σ-syntax
syntax Σ-syntax A (λ x → b) = Σ[ x ∈ A ] b

indΣ : {A : UU ℓ₁} {B : A → UU ℓ₂} {P : Σ[ x ∈ A ] B x → UU ℓ₃}
  → ((x : A) (y : B x) → P (x , y))
  → (z : Σ[ x ∈ A ] B x) → P z
indΣ f (x , y) = f x y

curry = indΣ

ev-pair : {A : UU ℓ₁} {B : A → UU ℓ₂} {P : Σ[ x ∈ A ] B x → UU ℓ₃}
  → ((z : Σ[ x ∈ A ] B x) → P z)
  → (x : A) (y : B x) → P (x , y)
ev-pair f x y = f (x , y)

uncurry = ev-pair

infixr 2 _×_
_×_ : (A : UU ℓ₁) (B : UU ℓ₂) → UU (ℓ₁ ⊔ ℓ₂)
A × B = Σ[ x ∈ A ] B

ind× : {A : UU ℓ₁} {B : UU ℓ₂} {P : A × B → UU ℓ₃}
  → ((x : A) (y : B) → P (x , y))
  → (z : A × B) → P z
ind× f (x , y) = f x y

-- Exercises

predℤ : ℤ → ℤ
predℤ (inl n) = in-neg (suc n)
predℤ (inr (inl ＊)) = in-neg zero
predℤ (inr (inr zero)) = 0ℤ
predℤ (inr (inr (suc n))) = in-pos n

addℤ : ℤ → ℤ → ℤ
addℤ (inl m) (inl n) = inl (suc (m + n))
addℤ (inl m) (inr (inl ＊)) = inl m
addℤ (inl zero) (inr (inr zero)) = inr (inl ＊)
addℤ (inl zero) (inr (inr (suc n))) = inr (inr n)
addℤ (inl (suc m)) (inr (inr zero)) = inl m
addℤ (inl (suc m)) (inr (inr (suc n))) = addℤ (inl m) (inr (inr n))
addℤ (inr (inl ＊)) (inl n) = inl n
addℤ (inr (inr zero)) (inl zero) = inr (inl ＊)
addℤ (inr (inr (suc m))) (inl zero) = inr (inr m)
addℤ (inr (inr zero)) (inl (suc n)) = inl n
addℤ (inr (inr (suc m))) (inl (suc n)) = addℤ (inr (inr m)) (inl n)
addℤ (inr (inl ＊)) (inr (inl ＊)) = inr (inl ＊)
addℤ (inr (inl ＊)) (inr (inr n)) = inr (inr n)
addℤ (inr (inr m)) (inr (inl ＊)) = inr (inr m)
addℤ (inr (inr m)) (inr (inr n)) = inr (inr (suc (m + n)))

negℤ : ℤ → ℤ
negℤ (inl n) = in-pos n
negℤ (inr (inl ＊)) = 0ℤ
negℤ (inr (inr n)) = in-neg n

data Bool : UU where
  false true : Bool

ind-Bool : {P : Bool → UU ℓ₁}
  → P false
  → P true
  → (x : Bool) → P x
ind-Bool pf pt false = pf
ind-Bool pf pt true  = pt

neg-Bool : Bool → Bool
neg-Bool false = true
neg-Bool true = false

_∧_ : Bool → Bool → Bool
false ∧ q = false
true ∧ q = q

_∨_ : Bool → Bool → Bool
false ∨ q = q
true ∨ q = true

_↔_ : UU ℓ₁ → UU ℓ₂ → UU (ℓ₁ ⊔ ℓ₂)
A ↔ B = (A → B) × (B → A)
infixl 3 _↔_

4-3a1 : {P : UU ℓ₁}
  → ¬ (P × ¬ P)
4-3a1 (P , ¬P) = ¬P P

4-3a2 : {P : UU ℓ₁}
  → ¬ (P ↔ ¬ P)
4-3a2 {P = P} (P→¬P , ¬P→P) = P→¬P (¬P→P ¬P) (¬P→P ¬P)
  where
    ¬P : ¬ P
    ¬P P = P→¬P P P

4-3b1 : {P : UU ℓ₁}
  → P → ¬¬ P
4-3b1 P ¬P = ¬P P

4-3b2 : {P Q : UU ℓ₁}
  → (P → Q) → (¬¬ P → ¬¬ Q)
4-3b2 P→Q ¬¬P ¬Q = ¬¬P (λ P → ¬Q (P→Q P))

4-3b3 : {P Q : UU ℓ₁}
  → (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
4-3b3 P→¬¬Q ¬¬P ¬Q = ¬¬P (λ P → P→¬¬Q P ¬Q)

4-3c1 : {P : UU ℓ₁}
  → ¬¬ (¬¬ P → P)
4-3c1 ¬[¬¬P→P] = ¬[¬¬P→P] (λ ¬¬P → ind𝟘 (¬¬P (λ P → ¬[¬¬P→P] λ _ → P)))

data list (A : UU ℓ₁) : UU ℓ₁ where
  nil : list A
  cons : A → list A → list A

ind-list : {A : UU ℓ₁} {P : list A → UU ℓ₂}
  → P nil
  → ((a : A) (as : list A) → P as → P (cons a as))
  → (as : list A) → P as
ind-list pnil pcons nil = pnil
ind-list pnil pcons (cons a as) = pcons a as (ind-list pnil pcons as)

fold-list : {A : UU ℓ₁} {B : UU ℓ₂}
  → B
  → (A → B → B)
  → list A → B
fold-list b μ nil = b
fold-list b μ (cons a as) = μ a (fold-list b μ as)

map-list : {A : UU ℓ₁} {B : UU ℓ₂}
  → (A → B)
  → list A → list B
map-list f = fold-list nil (λ a bs → cons (f a) bs)

length-list : {A : UU ℓ₁}
  → list A → ℕ
length-list = fold-list zero (const suc)

sum-list : list ℕ → ℕ
sum-list = fold-list zero _+_

product-list : list ℕ → ℕ
product-list = fold-list (suc zero) _*_

concat-list : {A : UU ℓ₁}
  → list A → list A → list A
concat-list nil as' = as'
concat-list (cons a as) as' = cons a (concat-list as as')

_++_ = concat-list

flatten-list : {A : UU ℓ₁}
  → list (list A) → list A
flatten-list = fold-list nil concat-list

reverse-list : {A : UU ℓ₁}
  → list A → list A
reverse-list nil = nil
reverse-list (cons a as) = (reverse-list as) ++ (cons a nil)
