Natural Number - ℕ

```agda

{-# OPTIONS --without-K --safe #-}

module Natural-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
open import Judgmental
open import Pi-Type

private variable i : Level

-- ℕ-formation Rule
data ℕ : 𝓤₀ where
  -- ℕ-introduciton rules
  0ℕ : ℕ   
  succℕ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

-- Induction Principle of ℕ
ℕ-ind : {P : ℕ → 𝓤 i}
  → P 0ℕ
  → Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n))
    ------------------------------
  → Π[ n ⦂ ℕ ] P n
ℕ-ind p₀ pₛ 0ℕ = p₀
ℕ-ind p₀ pₛ (succℕ n) = pₛ n (ℕ-ind p₀ pₛ n)

indℕ : {P : ℕ → 𝓤 i}
  → P 0ℕ ⇒ Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)) ⇒ Π[ n ⦂ ℕ ] P n
indℕ = ℕ-ind

-- ℕ-computation Rules
ℕ-comp-p₀ : {P : ℕ → 𝓤 i}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)))
    -------------------------------------
  → indℕ p₀ pₛ 0ℕ ≐ p₀
ℕ-comp-p₀ p₀ pₛ = equal

ℕ-comp-pₛ : {P : ℕ → 𝓤 i}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)))
    ----------------------------------------------------
  → (n : ℕ)
  → indℕ p₀ pₛ (succℕ n) ≐ pₛ n (indℕ p₀ pₛ n)
ℕ-comp-pₛ p₀ pₛ n = equal

-- Addition on ℕ
add-zeroℕ :
  ℕ
  → ℕ
add-zeroℕ m = m

add-succℕ :
  ℕ
  → (ℕ ⇒ (ℕ ⇒ ℕ))
add-succℕ m n x = succℕ x

addℕ′ : ℕ ⇒ ℕ ⇒ ℕ
addℕ′ m = indℕ (add-zeroℕ m) (add-succℕ m)

-- Pattern matching
addℕ : ℕ ⇒ ℕ ⇒ ℕ
addℕ m 0ℕ = m
addℕ m (succℕ n) = succℕ (addℕ m n)

_+_ = addℕ
infixl 6 _+_

mulℕ : ℕ ⇒ ℕ ⇒ ℕ
mulℕ m 0ℕ = 0ℕ
mulℕ m (succℕ n) = addℕ m (mulℕ m n)

_·_ = mulℕ
infixl 7 _·_
```
