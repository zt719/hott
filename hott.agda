module HoTT where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

{- Univerese -}
variable i j k l : Level

{- Judgmental Equality -}
data _≐_ {A : 𝓤 i} (x : A) : A → 𝓤 i where
  equal : x ≐ x
infix 4 _≐_

postulate
  ext : {A : 𝓤 i} {B : A → 𝓤 j} {f g : (x : A) → B x}
    → ((x : A) → f x ≐ g x)
      -------------------
    → (λ x → f x) ≐ (λ x → g x)

{- Dependent Function Type -}

Π : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Π A B = (x : A) → B x
syntax Π A (λ x → b) = Π[ x ⦂ A ] b

ƛ : {A : 𝓤 i} {B : A → 𝓤 j}
  → ((x : A) → B x)
    ---------------
  → Π[ x ⦂ A ] B x
ƛ b = λ x → b x

ƛ-eq : {A : 𝓤 i} {B : A → 𝓤 j} {b b′ : (x : A) → B x}
  → ((x : A) → b x ≐ b′ x)
    --------------------------
  → (λ x → b x) ≐ (λ x → b′ x)
ƛ-eq = ext

ev : {A : 𝓤 i} {B : A → 𝓤 j}
  → (f : Π[ x ⦂ A ] B x)
    -------------------
  → (x : A) → B x
ev f x = f x

ev-eq : {A : 𝓤 i} {B : A → 𝓤 j} {f f′ : Π[ x ⦂ A ] B x}
  → f ≐ f′
    --------------------
  → (x : A) → f x ≐ f′ x
ev-eq equal x = equal

β : {A : 𝓤 i} {B : A → 𝓤 j}
  → (b : (x : A) → B x)
    -----------------------------
  → (x : A) → (λ y → b y) x ≐ b x
β b x = equal

η : {A : 𝓤 i} {B : A → 𝓤 j}
  → (f : Π[ x ⦂ A ] B x)
    --------------------
  → (λ x → f x) ≐ f
η = λ f → equal

{- Function Type -}
_⇒_ : 𝓤 i → 𝓤 j → 𝓤 (i ⊔ j)
A ⇒ B = Π[ x ⦂ A ] B
infixr  0 _⇒_

ƛ-f : {A : 𝓤 i} {B : 𝓤 j}
  → ((x : A) → B)
    -------------
  → A ⇒ B
ƛ-f = ƛ

ev-f : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
    -----------
  → (x : A) → B
ev-f = ev

β-f : {A : 𝓤 i} {B : 𝓤 j}
  → (b : (x : A) → B)
    -----------------------------
  → (x : A) → (λ y → b y) x ≐ b x
β-f = β

η-f : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
    ---------------
  → (λ x → f x) ≐ f
η-f = η

id : {A : 𝓤 i}
  → A ⇒ A
id = λ x → x

_ : {A : 𝓤 i}
  → id ≐ (λ (x : A) → x)
_ = equal

comp : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k}
  → (B ⇒ C)
  → (A ⇒ B)
  → (A ⇒ C)
comp = λ g f x → g (f x)

_∘_ = comp
infix 9 _∘_

_ : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 j} {D : 𝓤 l}
  → (f : A ⇒ B)
  → (g : B ⇒ C)
  → (h : C ⇒ D)
  → (h ∘ g) ∘ f ≐ h ∘ (g ∘ f)
_ = λ f g h → equal

_ : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → id ∘ f ≐ f
_ = λ f → equal

_ : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → f ∘ id ≐ f
_ = λ f → equal

{-
-- Exercises
_ : {A : 𝓤 i} {B : A → Type}
  → (f g : Π[ x ⦂ A ] B x)
  → ((x : A) → f x ≐ g x)
    -------------------
  → f ≐ g
_ = λ f g → ƛ-eq 

-- Constant Function
const : {A : 𝓤 i} {B : 𝓤 j}
  → (y : B)
  → (A ⇒ B)
const y = λ _ → y

_ : {A B C : Type}
  → (f : A → B)
  → (z : C)
  → const z ∘ f ≐ const z
_ = λ f z → equal

{-
_ : {A B C : Type}
  → (g : B → C)
  → (y : B)
  → g ∘ const {A} y ≐ const {A} (g y)
_ = λ g y → η (λ x → equal)
-}

σ : {A : 𝓤 i} {B : 𝓤 j} {C : A → B → Type}
  → ((x : A) → (y : B) → C x y)
  → ((y : B) → (x : A) → C x y)
σ = λ f y x → f x y

_ : {A : 𝓤 i} {B : 𝓤 j} {C : A → B → Type}
  → σ {B} {A} ∘ σ {A} {B} ≐ id {(x : A) (y : B) → C x y}
_ = equal

{- Natural Number Type -}
data ℕ : Type where -- ℕ-formation
  0ℕ : ℕ            -- ℕ-intro zero elemnt
  succℕ : ℕ ⇒ ℕ     -- ℕ-intro succesor function

-- Induction Principle of ℕ
ℕ-ind : {P : ℕ → Type}
  → P 0ℕ
  → Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n))
    ------------------------------
  → Π[ n ⦂ ℕ ] P n
ℕ-ind p₀ pₛ 0ℕ = p₀
ℕ-ind p₀ pₛ (succℕ n) = pₛ n (ℕ-ind p₀ pₛ n)

indℕ : {P : ℕ → Type}
  → P 0ℕ ⇒ Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)) ⇒ Π[ n ⦂ ℕ ] P n
indℕ = ℕ-ind

-- Computation rules of ℕ
ℕ-comp-p₀ : {P : ℕ → Type}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)))
    -------------------------------------
  → indℕ p₀ pₛ 0ℕ ≐ p₀
ℕ-comp-p₀ p₀ pₛ = equal

ℕ-comp-pₛ : {P : ℕ → Type}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)))
    ----------------------------------------------------
  → (n : ℕ) → indℕ p₀ pₛ (succℕ n) ≐ pₛ n (indℕ p₀ pₛ n)
ℕ-comp-pₛ p₀ pₛ n = equal

-- Addition on ℕ
addℕ : ℕ ⇒ ℕ ⇒ ℕ
addℕ m 0ℕ = m
addℕ m (succℕ n) = succℕ (addℕ m n)

fib : ℕ ⇒ ℕ
fib 0ℕ = 0ℕ
fib (succℕ 0ℕ) = succℕ 0ℕ
fib (succℕ (succℕ n)) = addℕ (fib (succℕ n)) (fib n)

mulℕ : ℕ ⇒ ℕ ⇒ ℕ
mulℕ m 0ℕ = 0ℕ
mulℕ m (succℕ n) = addℕ m (mulℕ m n)


{- Unit Type -}

data 𝟙 : Type where
  * : 𝟙

ind𝟙 : {P : 𝟙 → Type}
  → P * ⇒ Π[ x ⦂ 𝟙 ] P x
ind𝟙 p* * = p*

𝟙-comp : {P : 𝟙 → Type}
  → (p* : P *)
  → ind𝟙 {P} p* * ≐ p*
𝟙-comp = λ p* → equal


{- Empty Type -}
data Φ : Type where

indΦ : {P : Φ → Type}
  → Π[ x ⦂ Φ ] P x
indΦ = λ ()

ex-falso : {A : 𝓤 i}
  → Φ ⇒ A
ex-falso = indΦ

¬_ : Type → Type
¬ A = A → Φ
infix  1  ¬_

is-empty : Type → Type
is-empty A = A → Φ

_ : {P Q : Type}
  → (P ⇒ Q) ⇒ (¬ Q ⇒ ¬ P)
_ = λ p→q ¬q p → ¬q (p→q p)

data _+_ (A B : Type) : Type where
  inl : A ⇒ A + B
  inr : B ⇒ A + B
infix  1 _+_

ind+ : {A : 𝓤 i} {B : 𝓤 j} {P : A + B → Type}
  → Π[ x ⦂ A ] P (inl x) ⇒ Π[ y ⦂ B ] P (inr y) ⇒ Π[ z ⦂ A + B ] P z
ind+ f g (inl x) = f x
ind+ f g (inr y) = g y

ind+′ : {A B X : Type}
  → (A ⇒ X) ⇒ (B ⇒ X) ⇒ (A + B ⇒ X)
ind+′ {A} {B} {P} = ind+ {A} {B} {λ _ → P}

_∔_ : {A A′ B B′ : Type}
  → (A ⇒ A′)
  → (B ⇒ B′)
  → (A + B ⇒ A′ + B′)
(f ∔ g) (inl x) = inl (f x)
(f ∔ g) (inr y) = inr (g y)

_ : {A : 𝓤 i} {B : 𝓤 j}
  → is-empty B ⇒ A + B ⇒ A
_ = λ ¬b → lemma id (ex-falso ∘ ¬b)
  where
  lemma : {A : 𝓤 i} {B : 𝓤 j}
    → (f : A ⇒ A)
    → (g : B ⇒ A)
    → A + B ⇒ A
  lemma f g (inl x) = f x
  lemma f g (inr y) = g y

{- Integer Type -}
ℤ : Type
ℤ = ℕ + (𝟙 + ℕ)

succℤ : ℤ ⇒ ℤ
succℤ (inl 0ℕ) = inr (inl *)
succℤ (inl (succℕ n)) = inl n
succℤ (inr (inl *)) = inr (inr 0ℕ)
succℤ (inr (inr n)) = inr (inr (succℕ n))

predℤ : ℤ ⇒ ℤ
predℤ (inl n) = inl (succℕ n)
predℤ (inr (inl *)) = inl 0ℕ
predℤ (inr (inr 0ℕ)) = inr (inl *)
predℤ (inr (inr (succℕ n))) = inr (inr n)

addℤ : ℤ ⇒ ℤ ⇒ ℤ
addℤ m (inl 0ℕ) = predℤ m
addℤ m (inl (succℕ n)) = addℤ (predℤ m) (inl n)
addℤ m (inr (inl *)) = m
addℤ m (inr (inr 0ℕ)) = succℤ m
addℤ m (inr (inr (succℕ n))) = addℤ (succℤ m) (inr (inr n))

negℤ : ℤ ⇒ ℤ
negℤ (inl n) = inr (inr n)
negℤ (inr (inl *)) = inr (inl *)
negℤ (inr (inr n)) = inl n

{- Dependent Pair Type -}
data Σ (A : Type) (B : A → Type) : Type where
  _,_ : Π[ x ⦂ A ] (B x ⇒ Σ A B)

Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ A B

syntax Σ A (λ x → b) = Σ[ x ⦂ A ] b

indΣ : {A : 𝓤 i} {B : A → Type} {P : Σ[ x ⦂ A ] B x → Type}
  → Π[ x ⦂ A ] Π[ y ⦂ B x ] P (x , y) ⇒ Π[ z ⦂ Σ[ x ⦂ A ] B x ] P z
indΣ f (x , y) = f x y

curry = indΣ

pr₁ : {A : 𝓤 i} {B : A → Type}
  → Σ[ x ⦂ A ] B x ⇒ A
pr₁ (x , y) = x

pr₂ : {A : 𝓤 i} {B : A → Type}
  → Π[ p ⦂ Σ[ x ⦂ A ] B x ] B (pr₁ p)
pr₂ (x , y) = y

ev-pair : {A : 𝓤 i} {B : A → Type} {P : Σ[ x ⦂ A ] B x → Type}
  → Π[ z ⦂ Σ[ x ⦂ A ] B x ] P z ⇒ Π[ x ⦂ A ] Π[ y ⦂ B x ] P (x , y)
ev-pair f x y = f (x , y)

uncurry = ev-pair

{- Product Type -}
_×_ : (A B : Type) → Type
A × B = Σ[ x ⦂ A ] B
infix  0 _×_

ind× : {A : 𝓤 i} {B : 𝓤 j} {P : A × B → Type}
  → Π[ x ⦂ A ] Π[ y ⦂ B ] P (x , y) ⇒ Π[ z ⦂ A × B ] P z
ind× f (x , y) = f x y

{- Boolean Type -}
data Bool : Type where
  false : Bool
  true : Bool
  
ind-Bool : {P : Bool → Type}
  → P false ⇒ P true ⇒ Π[ x ⦂ Bool ] P x
ind-Bool p₀ p₁ false = p₀
ind-Bool p₀ p₁ true  = p₁

neg-Bool : Bool ⇒ Bool
neg-Bool = ind-Bool true false

_∧_ : Bool ⇒ Bool ⇒ Bool
false ∧ y = false
true ∧ y = y

_∨_ : Bool ⇒ Bool ⇒ Bool
false ∨ y = y
true ∨ y = true

_⇔_ : Type → Type → Type
P ⇔ Q = (P ⇒ Q) × (Q ⇒ P)
infix 0  _⇔_

{- List Type -}
data List (A : Type) : Type where
  nil : List A
  cons : A ⇒ List A ⇒ List A

fold-list : {A : 𝓤 i} {B : 𝓤 j}
  → (b : B)
  → (μ : A ⇒ B ⇒ B)
  → List A ⇒ B
fold-list b μ nil = b
fold-list b μ (cons x xs) = μ x (fold-list b μ xs)

map-list : {A : 𝓤 i} {B : 𝓤 j}
  → (A ⇒ B) ⇒ List A ⇒ List B
map-list f = fold-list nil (λ a bs → cons (f a) bs)

{- Identity Type -}
data _≡_ {A : 𝓤 i} : A → A → Type where
  refl : (a : A) → a ≡ a
infix  4 _≡_

ind-eqₐ : {A : 𝓤 i} {a : A} {P : (x : A) → a ≡ x → Type}
  → P a (refl a) ⇒ Π[ x ⦂ A ] Π[ p ⦂ a ≡ x ] P x p
ind-eqₐ p a (refl a) = p

≡-intro : {A : 𝓤 i}
  → (a : A)
    -------
  → a ≡ a
≡-intro a = refl a

≡-elim : {A : 𝓤 i} 
  → (a : A)
  → (P : (x : A) (p : a ≡ x) → Type)
    ----------------------------
  → P a (refl a) ⇒ Π[ x ⦂ A ] Π[ p ⦂ a ≡ x ] P x p
≡-elim a P = ind-eqₐ

≡-comp : {A : 𝓤 i}
  → (a : A)
  → (P : (x : A) (p : a ≡ x) → Type)
    --------------------------------
  → (u : P a (refl a))
  → ind-eqₐ {A} {a} {λ a a≡x → P a a≡x} u a (refl a) ≐ u
≡-comp = λ a P u → equal

-- Groupoidal Structure of Types
concat : {A : 𝓤 i}
  → Π[ x ⦂ A ] Π[ y ⦂ A ] Π[ z ⦂ A ] (x ≡ y ⇒ y ≡ z ⇒ x ≡ z)
concat x x x (refl .x) (refl .x) = refl x

_∙_ = concat

inv : {A : 𝓤 i}
  → Π[ x ⦂ A ] Π[ y ⦂ A ] (x ≡ y ⇒ y ≡ x)
inv x .x (refl .x) = refl x
-}
