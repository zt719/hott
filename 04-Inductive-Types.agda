module 04-Inductive-Types where

open import 03-Natural-Numbers public

-- 4.2 The unit type
data 𝟏 : UU where
  ＊ : 𝟏 

ind𝟏 : {P : 𝟏 → UU i}
  → P ＊ → (x : 𝟏) → P x
ind𝟏 p ＊ = p

-- 4.3 The empty type
data Φ : UU where

indΦ : {P : Φ → UU i}
  → (x : Φ) → P x
indΦ = λ ()

ex-falso : {A : UU i}
  → Φ → A
ex-falso = indΦ

-- 4.3.2 Negation
¬_ : UU i → UU i
¬ A = A → Φ

¬¬_ : UU i → UU i
¬¬ A = ¬ A → Φ

is-empty : UU i → UU i 
is-empty A = A → Φ

-- 4.4 Corpoducts

data _∔_ (A : UU i) (B : UU j) : UU (i ⊔ j) where
  inl : A → A ∔ B
  inr : B → A ∔ B
infixr 2 _∔_

ind∔ : {A : UU i} {B : UU j} {P : A ∔ B → UU k}
  → ((x : A) → P (inl x))
  → ((y : B) → P (inr y))
  → (z : A ∔ B) → P z
ind∔ f g (inl x) = f x
ind∔ f g (inr y) = g y

[_,_] : {A : UU i} {B : UU j} {P : A ∔ B → UU k}
  → ((x : A) → P (inl x))
  → ((y : B) → P (inr y))
  → (z : A ∔ B) → P z
[ f , g ] = ind∔ f g

_∔∔_ : {A : UU i} {A′ : UU j} {B : UU k } {B′ : UU l}
  → (f : A → A′) (g : B → B′) → A ∔ B → A′ ∔ B′
(f ∔∔ g) (inl x) = inl (f x)
(f ∔∔ g) (inr y) = inr (g y)

-- 4.5 THe type of integers

ℤ = ℕ ∔ (𝟏 ∔ ℕ)

in-pos : ℕ → ℤ
in-pos = inr ∘ inr

in-neg : ℕ → ℤ
in-neg = inl

-1ℤ : ℤ
-1ℤ = in-neg 0ℕ

0ℤ : ℤ
0ℤ = inr (inl ＊)

1ℤ : ℤ
1ℤ = in-pos 0ℕ

indℤ : {P : ℤ → UU i}
  → P -1ℤ
  → ((n : ℕ) → P (in-neg n) → P (in-neg (succℕ n)))
  → P 0ℤ
  → P 1ℤ
  → ((n : ℕ) → P (in-pos n) → P (in-pos (succℕ n)))
  → (k : ℤ) → P k
indℤ p-1 p-s p0 p1 ps (inl 0ℕ) = p-1
indℤ p-1 p-s p0 p1 ps (inl (succℕ n))
  = p-s n (indℕ p-1 p-s n)
indℤ p-1 p-s p0 p1 ps (inr (inl ＊)) = p0
indℤ p-1 p-s p0 p1 ps (inr (inr 0ℕ)) = p1
indℤ p-1 p-s p0 p1 ps (inr (inr (succℕ n)))
  = ps n (indℕ p1 ps n)

succℤ : ℤ → ℤ
succℤ (inl 0ℕ) = 0ℤ
succℤ (inl (succℕ n)) = in-neg n
succℤ (inr (inl ＊)) = 1ℤ
succℤ (inr (inr n)) = in-pos (succℕ n)

-- 4.6 Dependent pair types

data Σ (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  _,_ : (x : A) → B x → Σ A B
infixr 4  _,_
syntax Σ A (λ x → b) = Σ x ∶ A , b

indΣ : {A : UU i} {B : A → UU j} {P : Σ x ∶ A , B x → UU k}
  → ((x : A) (y : B x) → P (x , y))
  → (z : Σ x ∶ A , B x) → P z
indΣ f (x , y) = f x y

pr₁ : {A : UU i} {B : A → UU j}
  → Σ x ∶ A , B x → A
pr₁ (x , y) = x

pr₂ : {A : UU i} {B : A → UU j}
  → (p : Σ x ∶ A , B x) → B (pr₁ p)
pr₂ (x , y) = y

curry = indΣ

ev-pair : {A : UU i} {B : A → UU j} {P : Σ x ∶ A , B x → UU k}
  → ((z : Σ x ∶ A , B x) → P z)
  → (x : A) (y : B x) → P (x , y)
ev-pair f x y = f (x , y)

uncurry = ev-pair

_×_ : (A : UU i) (B : UU j) → UU (i ⊔ j)
A × B = Σ x ∶ A , B
infix  2 _×_

ind× : {A : UU i} {B : UU j} {P : A × B → UU k}
  → ((x : A) (y : B) → P (x , y))
  → (z : A × B) → P z
ind× f (x , y) = f x y

-- Exercises

predℤ : ℤ → ℤ
predℤ (inl n) = in-neg (succℕ n)
predℤ (inr (inl ＊)) = in-neg 0ℕ
predℤ (inr (inr 0ℕ)) = 0ℤ
predℤ (inr (inr (succℕ n))) = in-pos n

addℤ : ℤ → ℤ → ℤ
addℤ (inl m) (inl n) = inl (succℕ (m + n))
addℤ (inl m) (inr (inl ＊)) = inl m
addℤ (inl 0ℕ) (inr (inr 0ℕ)) = inr (inl ＊)
addℤ (inl 0ℕ) (inr (inr (succℕ n))) = inr (inr n)
addℤ (inl (succℕ m)) (inr (inr 0ℕ)) = inl m
addℤ (inl (succℕ m)) (inr (inr (succℕ n))) = addℤ (inl m) (inr (inr n))
addℤ (inr (inl ＊)) (inl n) = inl n
addℤ (inr (inr 0ℕ)) (inl 0ℕ) = inr (inl ＊)
addℤ (inr (inr (succℕ m))) (inl 0ℕ) = inr (inr m)
addℤ (inr (inr 0ℕ)) (inl (succℕ n)) = inl n
addℤ (inr (inr (succℕ m))) (inl (succℕ n)) = addℤ (inr (inr m)) (inl n)
addℤ (inr (inl ＊)) (inr (inl ＊)) = inr (inl ＊)
addℤ (inr (inl ＊)) (inr (inr n)) = inr (inr n)
addℤ (inr (inr m)) (inr (inl ＊)) = inr (inr m)
addℤ (inr (inr m)) (inr (inr n)) = inr (inr (succℕ (m + n)))

negℤ : ℤ → ℤ
negℤ (inl n) = in-pos n
negℤ (inr (inl ＊)) = 0ℤ
negℤ (inr (inr n)) = in-neg n

data bool : UU where
  false : bool
  true : bool

ind-bool : {P : bool → UU i}
  → P false
  → P true
  → (x : bool) → P x
ind-bool pf pt false = pf
ind-bool pf pt true  = pt

neg-bool : bool → bool
neg-bool false = true
neg-bool true = false

_∧_ : bool → bool → bool
false ∧ q = false
true ∧ q = q

_∨_ : bool → bool → bool
false ∨ q = q
true ∨ q = true

_↔_ : UU i → UU j → UU (i ⊔ j)
A ↔ B = (A → B) × (B → A)
infixl 3 _↔_

4-3a1 : {P : UU i}
  → ¬ (P × ¬ P)
4-3a1 (P , ¬P) = ¬P P

4-3a2 : {P : UU i}
  → ¬ (P ↔ ¬ P)
4-3a2 {P = P} (P→¬P , ¬P→P) = P→¬P (¬P→P ¬P) (¬P→P ¬P)
  where
    ¬P : ¬ P
    ¬P P = P→¬P P P

4-3b1 : {P : UU i}
  → P → ¬¬ P
4-3b1 P ¬P = ¬P P

4-3b2 : {P Q : UU i}
  → (P → Q) → (¬¬ P → ¬¬ Q)
4-3b2 P→Q ¬¬P ¬Q = ¬¬P (λ P → ¬Q (P→Q P))

4-3b3 : {P Q : UU i}
  → (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
4-3b3 P→¬¬Q ¬¬P ¬Q = ¬¬P (λ P → P→¬¬Q P ¬Q)

4-3c1 : {P : UU i}
  → ¬¬ (¬¬ P → P)
4-3c1 ¬[¬¬P→P] = ¬[¬¬P→P] (λ ¬¬P → indΦ (¬¬P (λ P → ¬[¬¬P→P] λ _ → P)))

data list (A : UU i) : UU i where
  nil : list A
  cons : A → list A → list A

ind-list : {A : UU i} {P : list A → UU j}
  → P nil
  → ((a : A) (as : list A) → P as → P (cons a as))
  → (as : list A) → P as
ind-list pnil pcons nil = pnil
ind-list pnil pcons (cons a as) = pcons a as (ind-list pnil pcons as)

fold-list : {A : UU i} {B : UU j}
  → B
  → (A → B → B)
  → list A → B
fold-list b μ nil = b
fold-list b μ (cons a as) = μ a (fold-list b μ as)

map-list : {A : UU i} {B : UU j}
  → (A → B)
  → list A → list B
map-list f = fold-list nil (λ a bs → cons (f a) bs)

length-list : {A : UU i}
  → list A → ℕ
length-list = fold-list 0ℕ (const succℕ)

sum-list : list ℕ → ℕ
sum-list = fold-list 0ℕ _+_

product-list : list ℕ → ℕ
product-list = fold-list (succℕ 0ℕ) _*_

concat-list : {A : UU i}
  → list A → list A → list A
concat-list nil as' = as'
concat-list (cons a as) as' = cons a (concat-list as as')

_++_ = concat-list

flatten-list : {A : UU i}
  → list (list A) → list A
flatten-list = fold-list nil concat-list

reverse-list : {A : UU i}
  → list A → list A
reverse-list nil = nil
reverse-list (cons a as) = (reverse-list as) ++ (cons a nil)
