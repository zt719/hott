module 03-Natural-Numbers where

open import 02-Dependent-Function-Types public

-- 3.1 The formal specification of the type of ℕ
data ℕ : UU₀ where
  0ℕ : ℕ   
  succℕ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

indℕ : {P : ℕ → UU i}
  → P 0ℕ
  → ((n : ℕ) → P n → P (succℕ n))
  → ((n : ℕ ) → P n)
indℕ p₀ pₛ 0ℕ = p₀
indℕ p₀ pₛ (succℕ n) = pₛ n (indℕ p₀ pₛ n)

-- 3.2 Addition on the ℕ

add-zeroℕ : ℕ → ℕ
add-zeroℕ m = m

add-succℕ : ℕ → ℕ → ℕ → ℕ
add-succℕ m n x = succℕ x

addℕ : ℕ → ℕ → ℕ
addℕ m = indℕ (add-zeroℕ m) (add-succℕ m)

-- 3.3 Pattern matching

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
m + 0ℕ = m
m + succℕ n = succℕ (m + n)
{-# BUILTIN NATPLUS _+_ #-}

-- Exercises

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
0ℕ * n = 0ℕ
succℕ m * n = m * n + n
{-# BUILTIN NATTIMES _*_ #-}

minℕ : ℕ → ℕ → ℕ
minℕ 0ℕ n = 0ℕ
minℕ m 0ℕ = 0ℕ
minℕ (succℕ m) (succℕ n) = succℕ (minℕ m n)

maxℕ : ℕ → ℕ → ℕ
maxℕ 0ℕ n = n
maxℕ m 0ℕ = m
maxℕ (succℕ m) (succℕ n) = succℕ (maxℕ m n)

triℕ : ℕ → ℕ
triℕ 0ℕ = 0ℕ
triℕ (succℕ n) = triℕ n + succℕ n

facℕ : ℕ → ℕ
facℕ 0ℕ = succℕ 0ℕ
facℕ (succℕ n) = facℕ n * succℕ n

binomialℕ : ℕ → ℕ → ℕ
binomialℕ 0ℕ 0ℕ = succℕ 0ℕ
binomialℕ 0ℕ (succℕ m) = 0ℕ
binomialℕ (succℕ n) 0ℕ = 0ℕ
binomialℕ (succℕ n) (succℕ m)
  = binomialℕ n m + binomialℕ n (succℕ m)

fibℕ : ℕ → ℕ
fibℕ 0ℕ = 0ℕ
fibℕ (succℕ 0ℕ) = succℕ 0ℕ
fibℕ (succℕ (succℕ n)) = fibℕ (succℕ n) + fibℕ n
