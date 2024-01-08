Natural Number - ℕ

```agda

{-# OPTIONS --without-K --safe #-}

module Natural-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

data ℕ : 𝓤₀ where
  0ℕ : ℕ   
  succℕ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

addℕ : ℕ → ℕ → ℕ
addℕ m 0ℕ = m
addℕ m (succℕ n) = succℕ (addℕ m n)

_+_ = addℕ
infixl 6 _+_

mulℕ : ℕ → ℕ → ℕ
mulℕ m 0ℕ = 0ℕ
mulℕ m (succℕ n) = addℕ m (mulℕ m n)

_·_ = mulℕ
infixl 7 _·_
```
