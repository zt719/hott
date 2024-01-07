Identity Type - ≡

```agda

{-# OPTIONS --without-K --safe #-}

module Identity-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

open import Pi-Type using (id)

private variable i j : Level

data _≡_ {A : 𝓤 i} : A → A → 𝓤 i where
  refl : (a : A) → a ≡ a
infix  4 _≡_

concat : {A : 𝓤 i} {x y z : A}
  → x ≡ y → y ≡ z → x ≡ z
concat (refl x) (refl x) = refl x

_∙_ = concat

inv : {A : 𝓤 i} {x y : A}
  → x ≡ y → y ≡ x
inv (refl x) = refl x

ap : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A → B)
  → {x y : A}
  → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

tr : {A : 𝓤 i}
  → (B : A → 𝓤 j)
  → {x y : A}
  → x ≡ y
  → B x → B y
tr B (refl x) = id (B x)

```
