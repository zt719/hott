module 03-Natural-Numbers where

open import 02-Dependent-Function-Types public

-- 3.1 The formal specification of the type of ℕ
data ℕ : UU where
  zero : ℕ   
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

indℕ : {P : ℕ → UU ℓ₁}
  → P zero
  → ((n : ℕ) → P n → P (suc n))
  → ((n : ℕ ) → P n)
indℕ p₀ pₛ zero = p₀
indℕ p₀ pₛ (suc n) = pₛ n (indℕ p₀ pₛ n)

-- 3.2 Addition on the ℕ

add-zero : ℕ → ℕ
add-zero m = m

add-suc : ℕ → ℕ → ℕ → ℕ
add-suc m n x = suc x

addℕ : ℕ → ℕ → ℕ
addℕ m = indℕ (add-zero m) (add-suc m)

-- 3.3 Pattern matching

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
m + zero = m
m + suc n = suc (m + n)
{-# BUILTIN NATPLUS _+_ #-}

-- Exercises

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = m * n + n
{-# BUILTIN NATTIMES _*_ #-}

minℕ : ℕ → ℕ → ℕ
minℕ zero zero = zero
minℕ zero (suc n) = zero
minℕ (suc m) zero = zero
minℕ (suc m) (suc n) = suc (minℕ m n)

maxℕ : ℕ → ℕ → ℕ
maxℕ zero zero = zero
maxℕ zero (suc n) = suc n
maxℕ (suc m) zero = suc m
maxℕ (suc m) (suc n) = suc (maxℕ m n)

triℕ : ℕ → ℕ
triℕ zero = zero
triℕ (suc n) = triℕ n + suc n

facℕ : ℕ → ℕ
facℕ zero = suc zero
facℕ (suc n) = facℕ n * suc n

binomialℕ : ℕ → ℕ → ℕ
binomialℕ zero zero = suc zero
binomialℕ zero (suc n) = zero
binomialℕ (suc m) zero = zero
binomialℕ (suc m) (suc n)
  = binomialℕ n m + binomialℕ n (suc m)

fibℕ : ℕ → ℕ
fibℕ zero = zero
fibℕ (suc zero) = suc zero
fibℕ (suc (suc n)) = fibℕ (suc n) + fibℕ n
