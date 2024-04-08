module 04-Inductive-Types where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)                           
open import 03-Natural-Numbers public

private variable 𝓲 𝓳 𝓴 𝓱 : Level

-- 𝟙-formation Rule
data 𝟙 : 𝓤₀ where
  ＊ : 𝟙

ind𝟙 : {P : 𝟙 → 𝓤 𝓲}
  → P ＊
  → Π[ x ∶ 𝟙 ] P x
ind𝟙 p ＊ = p

-- φ-formaiton Rule
data Φ : 𝓤₀ where

indΦ : {P : Φ → 𝓤 𝓲}
  → (x : Φ) → P x
indΦ = λ ()

ex-falso : {A : 𝓤 𝓲}
  → Φ → A
ex-falso = indΦ

-- Negation
¬_ : 𝓤 𝓲 → 𝓤 𝓲
¬ A = A → Φ

is-empty : 𝓤 𝓲 → 𝓤 𝓲 
is-empty A = A → Φ

¬¬_ : 𝓤 𝓲 → 𝓤 𝓲 
¬¬ A = ¬ ¬ A

¬¬¬_ : 𝓤 𝓲 → 𝓤 𝓲 
¬¬¬ A = ¬ ¬ ¬ A

-- Proof of Negation
_ : {P : 𝓤 𝓲 } {Q : 𝓤 𝓲}
  → (P → Q) → (¬ Q → ¬ P)
_ = λ p→q ¬q p → ¬q (p→q p)

data _∔_ (A : 𝓤 𝓲) (B : 𝓤 𝓳) : 𝓤 (𝓲 ⊔ 𝓳) where
  inl : A ⇒ A ∔ B
  inr : B ⇒ A ∔ B
infixr 2 _∔_

ind∔ : {A : 𝓤 𝓲} {B : 𝓤 𝓳} {P : A ∔ B → 𝓤 𝓴}
  → Π[ x ∶ A ] (P (inl x)) ⇒ Π[ y ∶ B ] (P (inr y)) ⇒ Π[ z ∶ A ∔ B ] (P z)
ind∔ f g (inl x) = f x
ind∔ f g (inr y) = g y

[_,_] : {A : 𝓤 𝓲} {B : 𝓤 𝓳} {P : A ∔ B → 𝓤 𝓴}
  → Π[ x ∶ A ] (P (inl x)) ⇒ Π[ y ∶ B ] (P (inr y)) ⇒ Π[ z ∶ A ∔ B ] (P z)
[ f , g ] = ind∔ f g

_∔∔_ : {A : 𝓤 𝓲} {A′ : 𝓤 𝓳} {B : 𝓤 𝓴 } {B′ : 𝓤 𝓱}
  → (f : A → A′) (g : B → B′)
  → (A ∔ B → A′ ∔ B′)
(f ∔∔ g) (inl x) = inl (f x)
(f ∔∔ g) (inr y) = inr (g y)


-- Dependent Pair Types
data Σ (A : 𝓤 𝓲) (B : A → 𝓤 𝓳) : 𝓤 (𝓲 ⊔ 𝓳) where
  _,_ : Π[ x ∶ A ] (B x → Σ A B)
infixr 4  _,_
syntax Σ A (λ x → b) = Σ[ x ∶ A ] b

indΣ : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳} {P : Σ[ x ∶ A ] B x → 𝓤 𝓴}
  → Π[ x ∶ A ] Π[ y ∶ B x ] P (x , y) ⇒ Π[ z ∶ Σ[ x ∶ A ] B x ] P z
indΣ f (x , y) = f x y

pr₁ : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Σ[ x ∶ A ] B x ⇒ A
pr₁ (x , y) = x

pr₂ : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π[ p ∶ Σ[ x ∶ A ] B x ] B (pr₁ p)
pr₂ (x , y) = y

curry = indΣ

ev-pair : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳} {P : Σ[ x ∶ A ] B x → 𝓤 𝓴}
  → Π[ z ∶ Σ[ x ∶ A ] B x ] P z
  → Π[ x ∶ A ] Π[ y ∶ B x ] P (x , y)
ev-pair f x y = f (x , y)

uncurry = ev-pair

_×_ : (A : 𝓤 𝓲) (B : 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
A × B = Σ[ x ∶ A ] B
infix  2 _×_

ind× : {A : 𝓤 𝓲} {B : 𝓤 𝓳} {P : A × B → 𝓤 𝓴}
  → Π[ x ∶ A ] Π[ y ∶ B ] P (x , y) → Π[ z ∶ A × B ] P z
ind× f (x , y) = f x y

_⇔_ : 𝓤 𝓲 → 𝓤 𝓳 → 𝓤 (𝓲 ⊔ 𝓳)
A ⇔ B = (A ⇒ B) × (B ⇒ A)
infixl 3 _⇔_

-- boolean
data bool : 𝓤₀ where
  false : bool
  true : bool

ind-bool : {P : bool → 𝓤 𝓲}
  → P false
  → P true
  → Π[ x ∶ bool ] P x
ind-bool pf pt false = pf
ind-bool pf pt true  = pt

neg-bool : bool ⇒ bool
neg-bool false = true
neg-bool true = false
