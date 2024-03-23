Natural Number - ℕ

```agda

{-# OPTIONS --without-K --safe #-}

module Naturals where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import Agda.Builtin.Equality
  renaming (_≡_ to _≐_; refl to equal)

open import Pi

private variable i : Level

-- ℕ-formation Rule
data ℕ : 𝓤₀ where
  -- ℕ-introduciton rules
  0ℕ : ℕ   
  succℕ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

-- Induction Principle of ℕ
indℕ : {P : ℕ → 𝓤 i}
  → P 0ℕ
  ⇒ Π[ n ⦂ ℕ ] (P n → P (succℕ n))
  ⇒ Π[ n ⦂ ℕ ] (P n)
indℕ p₀ pₛ 0ℕ = p₀
indℕ p₀ pₛ (succℕ n) = pₛ n (indℕ p₀ pₛ n)

-- ℕ-computation Rules
{-
ℕ-comp-p₀ : {P : ℕ → 𝓤 i}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n → P (succℕ n)))
    -------------------------------------
  → indℕ p₀ pₛ 0ℕ ≐ p₀
ℕ-comp-p₀ p₀ pₛ = equal

ℕ-comp-pₛ : {P : ℕ → 𝓤 i}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n → P (succℕ n)))
    ----------------------------------------------------
  → (n : ℕ)
  → indℕ p₀ pₛ (succℕ n) ≐ pₛ n (indℕ p₀ pₛ n)
ℕ-comp-pₛ p₀ pₛ n = equal
-}

-- Addition on ℕ
add-zeroℕ : ℕ → ℕ
add-zeroℕ m = m

add-succℕ : ℕ → ℕ → ℕ → ℕ
add-succℕ m n x = succℕ x

--addℕ′ : ℕ → ℕ → ℕ
--addℕ′ m = indℕ (add-zeroℕ m) (add-succℕ m)

-- Pattern matching
addℕ : ℕ → ℕ → ℕ
addℕ m 0ℕ = m
addℕ m (succℕ n) = succℕ (addℕ m n)

_+_ = addℕ
infixl 6 _+_

mulℕ : ℕ → ℕ → ℕ
mulℕ 0ℕ n = 0ℕ
mulℕ (succℕ m) n = addℕ (mulℕ m n) n

_*_ = mulℕ
infixl 7 _*_

```
