Coproduct Type

```agda

{-# OPTIONS --without-K --safe #-}

module Coproduct-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
open import Judgmental
open import Pi-Type
open import Empty-Type using (is-empty; ex-falso)

private variable i j k l : Level

data _∔_ (A : 𝓤 i) (B : 𝓤 j) : 𝓤 (i ⊔ j) where
  inl : A ⇒ A ∔ B
  inr : B ⇒ A ∔ B
infix  1 _∔_

ind∔ : {A : 𝓤 i} {B : 𝓤 j} {P : A ∔ B → 𝓤 k}
  → Π[ x ⦂ A ] P (inl x) ⇒ Π[ y ⦂ B ] P (inr y) ⇒ Π[ z ⦂ A ∔ B ] P z
ind∔ f g (inl x) = f x
ind∔ f g (inr y) = g y

ind∔′ : {A : 𝓤 i} {B : 𝓤 j} {X : 𝓤 k}
  → (A ⇒ X) ⇒ ((B ⇒ X) ⇒ (A ∔ B ⇒ X))
ind∔′ = ind∔

_⊹_ : {A : 𝓤 i} {B : 𝓤 j} {A′ : 𝓤 k} {B′ : 𝓤 l}
  → (f : A ⇒ A′)
  → (g : B ⇒ B′)
  → A ∔ B ⇒ A′ ∔ B′
(f ⊹ g) (inl x) = inl (f x)
(f ⊹ g) (inr y) = inr (g y)

lemma0 : {A : 𝓤 i} {B : 𝓤 j}
  → is-empty B ⇒ (A ∔ B ⇒ A)
lemma0 {A = A} ¬b = ind∔ id (ex-falso ∘ ¬b)

```
