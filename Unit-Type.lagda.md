Unit Type - 𝟙

```agda

{-# OPTIONS --without-K --safe #-}

module Unit-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
                           
data 𝟙 : 𝓤₀ where
  * : 𝟙

```
