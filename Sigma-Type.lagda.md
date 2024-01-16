```agda
{-# OPTIONS --without-K --safe #-}

module Sigma-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

open import Judgmental
open import Pi-Type

private variable i j k : Level

data Σ (A : 𝓤 i) (B : A → 𝓤 j) : 𝓤 (i ⊔ j) where
  _,_ : Π[ x ⦂ A ] (B x ⇒ Σ A B)
infixr 0  _,_

syntax Σ A (λ x → b) = Σ[ x ⦂ A ] b

indΣ : {A : 𝓤 i} {B : A → 𝓤 j} {P : Σ[ x ⦂ A ] B x → 𝓤 k}
  → Π[ x ⦂ A ] Π[ y ⦂ B x ] P (x , y) ⇒ Π[ z ⦂ Σ[ x ⦂ A ] B x ] P z
indΣ f (x , y) = f x y

pr₁ : {A : 𝓤 i} {B : A → 𝓤 j}
  → Σ[ x ⦂ A ] B x ⇒ A
pr₁ (x , y) = x

pr₂ : {A : 𝓤 i} {B : A → 𝓤 j}
  → Π[ p ⦂ Σ[ x ⦂ A ] B x ] B (pr₁ p)
pr₂ (x , y) = y

curry = indΣ

ev-pair : {A : 𝓤 i} {B : A → 𝓤 j} {P : Σ[ x ⦂ A ] B x → 𝓤 k}
  → Π[ z ⦂ Σ[ x ⦂ A ] B x ] P z ⇒ Π[ x ⦂ A ] Π[ y ⦂ B x ] P (x , y)
ev-pair f x y = f (x , y)

uncurry = ev-pair
```

Product

```agda
_×_ : (A : 𝓤 i) (B : 𝓤 j) → 𝓤 (i ⊔ j)
A × B = Σ[ x ⦂ A ] B
infix  2 _×_

ind× : {A : 𝓤 i} {B : 𝓤 j} {P : A × B → 𝓤 k}
  → Π[ x ⦂ A ] Π[ y ⦂ B ] P (x , y) ⇒ Π[ z ⦂ A × B ] P z
ind× f (x , y) = f x y

comp× : {A : 𝓤 i} {B : 𝓤 j} {P : A × B → 𝓤 k}
  → (g : Π[ x ⦂ A ] Π[ y ⦂ B ] P (x , y))
  → (x : A)
  → (y : B)
  → ind× {A = A} {B = B} {P = P} g (x , y) ≐ (g x y)
comp× = λ g x y → equal

```

Binary Sigma Type


```agda
