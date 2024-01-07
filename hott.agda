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

id : (A : 𝓤 i)
  → A ⇒ A
id A = λ x → x

_ : {A : 𝓤 i}
  → id A ≐ (λ x → x)
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
  → id B ∘ f ≐ f
_ = λ f → equal

_ : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → f ∘ id A ≐ f
_ = λ f → equal

const : {A : 𝓤 i} {B : 𝓤 j}
  → (y : B)
  → (A ⇒ B)
const y = λ _ → y

σ : {A : 𝓤 i} {B : 𝓤 j} {C : A → B → 𝓤 k}
  → ((x : A) → (y : B) → C x y)
  → ((y : B) → (x : A) → C x y)
σ = λ f y x → f x y

{- Natural Number Type -}
data ℕ : 𝓤 lzero where -- ℕ-formation
  0ℕ : ℕ            -- ℕ-intro zero elemnt
  succℕ : ℕ ⇒ ℕ     -- ℕ-intro succesor function

ℕ-ind : {P : ℕ → 𝓤 i}
  → P 0ℕ
  → Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n))
    ------------------------------
  → Π[ n ⦂ ℕ ] P n
ℕ-ind p₀ pₛ 0ℕ = p₀
ℕ-ind p₀ pₛ (succℕ n) = pₛ n (ℕ-ind p₀ pₛ n)

indℕ : {P : ℕ → 𝓤 i}
  → P 0ℕ ⇒ Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)) ⇒ Π[ n ⦂ ℕ ] P n
indℕ = ℕ-ind

ℕ-comp-p₀ : {P : ℕ → 𝓤 i}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)))
    -------------------------------------
  → indℕ p₀ pₛ 0ℕ ≐ p₀
ℕ-comp-p₀ p₀ pₛ = equal

ℕ-comp-pₛ : {P : ℕ → 𝓤 i}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)))
    ----------------------------------------------------
  → (n : ℕ) → indℕ p₀ pₛ (succℕ n) ≐ pₛ n (indℕ p₀ pₛ n)
ℕ-comp-pₛ p₀ pₛ n = equal

addℕ : ℕ ⇒ ℕ ⇒ ℕ
addℕ m 0ℕ = m
addℕ m (succℕ n) = succℕ (addℕ m n)

mulℕ : ℕ ⇒ ℕ ⇒ ℕ
mulℕ m 0ℕ = 0ℕ
mulℕ m (succℕ n) = addℕ m (mulℕ m n)


{- Unit Type -}

data 𝟙 : 𝓤 lzero where
  * : 𝟙

ind𝟙 : {P : 𝟙 → 𝓤 i}
  → P * ⇒ Π[ x ⦂ 𝟙 ] P x
ind𝟙 p* * = p*

𝟙-comp : {P : 𝟙 → 𝓤 i}
  → (p* : P *)
  → ind𝟙 {i} {P} p* * ≐ p*
𝟙-comp = λ p* → equal

{- Empty Type -}
data Φ : 𝓤 lzero where

indΦ : {P : Φ → 𝓤 i}
  → Π[ x ⦂ Φ ] P x
indΦ = λ ()

ex-falso : {A : 𝓤 i}
  → Φ ⇒ A
ex-falso = indΦ

¬_ : 𝓤 i → 𝓤 i
¬ A = A → Φ
infix  1  ¬_

is-empty : 𝓤 i → 𝓤 i
is-empty A = A → Φ

{- Coproduct Type -}
data _∔_ (A : 𝓤 i) (B : 𝓤 j) : 𝓤 (i ⊔ j) where
  inl : A ⇒ A ∔ B
  inr : B ⇒ A ∔ B
infix  1 _∔_

ind∔ : {A : 𝓤 i} {B : 𝓤 j} {P : A ∔ B → 𝓤 k}
  → Π[ x ⦂ A ] P (inl x) ⇒ Π[ y ⦂ B ] P (inr y) ⇒ Π[ z ⦂ A ∔ B ] P z
ind∔ f g (inl x) = f x
ind∔ f g (inr y) = g y

{-
_⇒∔_ : {A A′ B B′ : Type}
  → (A ⇒ A′)
  → (B ⇒ B′)
  → (A + B ⇒ A′ + B′)
(f ⇒∔ g) (inl x) = inl (f x)
(f ⇒∔ g) (inr y) = inr (g y)
-}

{-
_ : {A : 𝓤 i} {B : 𝓤 j}
  → is-empty B ⇒ A ∔ B ⇒ A
_ = λ ¬b → lemma (id A) (ex-falso ∘ ¬b)
  where
  lemma : {A : 𝓤 i} {B : 𝓤 j}
    → (f : A ⇒ A)
    → (g : B ⇒ A)
    → A ∔ B ⇒ A
  lemma f g (inl x) = f x
  lemma f g (inr y) = g y
-}

{- Integer Type -}
ℤ : 𝓤 lzero
ℤ = ℕ ∔ (𝟙 ∔ ℕ)

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
data Σ (A : 𝓤 i) (B : A → 𝓤 j) : 𝓤 (i ⊔ j) where
  _,_ : Π[ x ⦂ A ] (B x ⇒ Σ A B)

Sigma : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Sigma A B = Σ A B

syntax Σ A (λ x → b) = Σ[ x ⦂ A ] b

indΣ : {A : 𝓤 i} {B : A → 𝓤 j} {P : Σ[ x ⦂ A ] B x → 𝓤 k}
  → Π[ x ⦂ A ] Π[ y ⦂ B x ] P (x , y) ⇒ Π[ z ⦂ Σ[ x ⦂ A ] B x ] P z
indΣ f (x , y) = f x y

curry = indΣ

pr₁ : {A : 𝓤 i} {B : A → 𝓤 j}
  → Σ[ x ⦂ A ] B x ⇒ A
pr₁ (x , y) = x

pr₂ : {A : 𝓤 i} {B : A → 𝓤 j}
  → Π[ p ⦂ Σ[ x ⦂ A ] B x ] B (pr₁ p)
pr₂ (x , y) = y


ev-pair : {A : 𝓤 i} {B : A → 𝓤 j} {P : Σ[ x ⦂ A ] B x → 𝓤 k}
  → Π[ z ⦂ Σ[ x ⦂ A ] B x ] P z ⇒ Π[ x ⦂ A ] Π[ y ⦂ B x ] P (x , y)
ev-pair f x y = f (x , y)

uncurry = ev-pair

{- Product Type -}
_×_ : (A : 𝓤 i) (B : 𝓤 j) → 𝓤 (i ⊔ j)
A × B = Σ[ x ⦂ A ] B
infix  2 _×_

ind× : {A : 𝓤 i} {B : 𝓤 j} {P : A × B → 𝓤 k}
  → Π[ x ⦂ A ] Π[ y ⦂ B ] P (x , y) ⇒ Π[ z ⦂ A × B ] P z
ind× f (x , y) = f x y

pr₁-× : {A : 𝓤 i} {B : 𝓤 j} 
  → A × B ⇒ A 
pr₁-× = pr₁

pr₂-× : {A : 𝓤 i} {B : 𝓤 j}
  → A × B ⇒ B
pr₂-× = pr₂

{- Boolean Type -}
data Bool : 𝓤 lzero where
  false : Bool
  true : Bool
  
ind-Bool : {P : Bool → 𝓤 i}
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

{- List Type -}
data List (A : 𝓤 i) : 𝓤 i where
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
data _≡_ {A : 𝓤 i} : A → A → 𝓤 i where
  refl : (a : A) → a ≡ a
infix  4 _≡_

ind-eqₐ : {A : 𝓤 i} {a : A} {P : (x : A) → a ≡ x → 𝓤 j}
  → P a (refl a) ⇒ Π[ x ⦂ A ] Π[ p ⦂ a ≡ x ] P x p
ind-eqₐ p a (refl a) = p

≡-intro : {A : 𝓤 i}
  → (a : A)
    -------
  → a ≡ a
≡-intro a = refl a

≡-elim : {A : 𝓤 i} 
  → (a : A)
  → (P : (x : A) (p : a ≡ x) → 𝓤 j)
    ----------------------------------------------
  → P a (refl a) ⇒ Π[ x ⦂ A ] Π[ p ⦂ a ≡ x ] P x p
≡-elim a P = ind-eqₐ

≡-comp : {A : 𝓤 i}
  → (a : A)
  → (P : (x : A) (p : a ≡ x) → 𝓤 j)
    --------------------------------
  → (u : P a (refl a))
  → ind-eqₐ {i} {j} {A} {a} {λ a a≡x → P a a≡x} u a (refl a) ≐ u
≡-comp = λ a P u → equal

concat : {A : 𝓤 i} {x y z : A}
  → x ≡ y ⇒ y ≡ z ⇒ x ≡ z
concat (refl x) (refl x) = refl x

_∙_ = concat

inv : {A : 𝓤 i} {x y : A}
  → x ≡ y ⇒ y ≡ x
inv (refl x) = refl x

assoc-≡ : {A : 𝓤 i} {x y z w : A}
  → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc-≡ (refl x) (refl x) (refl x) = refl (refl x)

left-unit-≡ : {A : 𝓤 i} {x y : A}
  → (p : x ≡ y)
  → refl x ∙ p ≡ p
left-unit-≡ (refl x) = refl (refl x)

right-unit-≡ : {A : 𝓤 i} {x y : A}
  → (p : x ≡ y)
  → p ∙ refl y ≡ p
right-unit-≡ (refl x) = refl (refl x)

left-inv-≡ : {A : 𝓤 i} {x y : A}
  → (p : x ≡ y)
  → inv p ∙ p ≡ refl y
left-inv-≡ (refl x) = refl (refl x)

right-inv-≡ : {A : 𝓤 i} {x y : A}
  → (p : x ≡ y)
  → p ∙ inv p ≡ refl x
right-inv-≡ (refl x) = refl (refl x)

ap : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → {x y : A}
  → x ≡ y ⇒ f x ≡ f y
ap f (refl x) = refl (f x)

ap-id : {A : 𝓤 i}
  → {x y : A}
  → (p : x ≡ y)
  → p ≡ ap (id A)  p
ap-id (refl x) = refl (refl x)

ap-comp : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k}
  → (f : A → B)
  → (g : B → C)
  →  {x y : A}
  → (p : x ≡ y)
  → ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp f g (refl x) = refl (refl (g (f x)))

ap-refl : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A → B)
  → (x : A)
  → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-inv : {A : 𝓤 i} {B : 𝓤 j} {x y : A}
  → (f : A → B)
  → (p : x ≡ y)
  → ap f (inv p) ≡ inv (ap f p)
ap-inv {x = x} f (refl .x) = refl (refl (f x))

ap-concat : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k} {x y z : A}
  → (f : A → B)
  → (p : x ≡ y)
  → (q : y ≡ z)
  → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-concat {x = x} f (refl .x) (refl .x) = refl (refl (f x))

tr : {A : 𝓤 i}
  → (B : A → 𝓤 j)
  → {x y : A}
  → x ≡ y
  → B x → B y
tr B (refl x) = id (B x)

apd : {A : 𝓤 i} {B : A → 𝓤 j} {x y : A}
  → (f : (x : A) → B x)
  → (p : x ≡ y)
  → tr B p (f x) ≡ f y
apd f (refl x) = refl (f x)
