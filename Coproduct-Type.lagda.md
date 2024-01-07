Coproduct Type

```agda
module Coproduct-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

private variable i j k : Level

data _∔_ (A : 𝓤 i) (B : 𝓤 j) : 𝓤 (i ⊔ j) where
  inl : A → A ∔ B
  inr : B → A ∔ B
infix  1 _∔_

