Empty Type - Φ

```agda

{-# OPTIONS --without-K --safe #-}

module Empty-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

data Φ : 𝓤₀ where
