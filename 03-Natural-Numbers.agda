module 03-Natural-Numbers where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import 02-Dependent-Function-Types public

private variable 𝓲 : Level

-- ℕ-formation Rule
data ℕ : 𝓤₀ where
  -- ℕ-introduciton rules
  0ℕ : ℕ   
  succℕ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

-- 𝓲nduction Principle of ℕ
indℕ : {P : ℕ → 𝓤 𝓲}
  → P 0ℕ
  ⇒ Π[ n ∶ ℕ ] (P n ⇒ P (succℕ n))
  ⇒ Π[ n ∶ ℕ ] (P n)
indℕ p₀ pₛ 0ℕ = p₀
indℕ p₀ pₛ (succℕ n) = pₛ n (indℕ p₀ pₛ n)

ℕind = indℕ

-- Addition on ℕ
add-zeroℕ : ℕ ⇒ ℕ
add-zeroℕ m = m

add-succℕ : ℕ ⇒ ℕ ⇒ ℕ ⇒ ℕ
add-succℕ m n x = succℕ x

-- Pattern matching
addℕ : ℕ ⇒ ℕ ⇒ ℕ
addℕ m 0ℕ = m
addℕ m (succℕ n) = succℕ (addℕ m n)

_+_ = addℕ
infixl 6 _+_

mulℕ : ℕ ⇒ ℕ ⇒ ℕ
mulℕ 0ℕ n = 0ℕ
mulℕ (succℕ m) n = addℕ (mulℕ m n) n

_*_ = mulℕ
infixl 7 _*_
