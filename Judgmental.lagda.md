
```agda

{-# OPTIONS --without-K --safe #-}

module Judgmental where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

private variable i j k l : Level

data _≐_ {A : 𝓤 i} (x : A) : A → 𝓤 i where
  equal : x ≐ x
infix 4 _≐_
```
