```agda
module Coproducts where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import Agda.Builtin.Equality
  renaming (_≡_ to _≐_; refl to equal)

private variable i j k h : Level

open import Pi
open import Sigma

{-
data Σ (A : 𝓤 i) (B : A → 𝓤 j) : 𝓤 (i ⊔ j) where
  _,_ : Π[ x ⦂ A ] (B x → Σ A B)
infixr 4  _,_
-}

data _∔_ (A : 𝓤 i) (B : 𝓤 j) : 𝓤 (i ⊔ j) where
  inl : A ⇒ A ∔ B
  inr : B ⇒ A ∔ B
infixr 2 _∔_

ind∔ : {A : 𝓤 i} {B : 𝓤 j} {P : A ∔ B → 𝓤 k}
  → Π[ x ∶ A ] (P (inl x)) ⇒ Π[ y ∶ B ] (P (inr y)) ⇒ Π[ z ∶ A ∔ B ] (P z)
ind∔ f g (inl x) = f x
ind∔ f g (inr y) = g y

_∔∔_ : {A : 𝓤 i} {A′ : 𝓤 j} {B : 𝓤 k} {B′ : 𝓤 h}
  → (f : A → A′) (g : B → B′)
  → (A ∔ B → A′ ∔ B′)
(f ∔∔ g) (inl x) = inl (f x)
(f ∔∔ g) (inr y) = inr (g y)
  
  

```
