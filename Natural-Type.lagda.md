Natural Number - ℕ

```agda

{-# OPTIONS --without-K --safe #-}

module Natural-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

data ℕ : 𝓤₀ where
  0ℕ : ℕ   
  succℕ : ℕ → ℕ

addℕ : ℕ → ℕ → ℕ
addℕ m 0ℕ = m
addℕ m (succℕ n) = succℕ (addℕ m n)

mulℕ : ℕ → ℕ → ℕ
mulℕ m 0ℕ = 0ℕ
mulℕ m (succℕ n) = addℕ m (mulℕ m n)
```
