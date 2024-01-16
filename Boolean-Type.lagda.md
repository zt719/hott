```agda

{-# OPTIONS --without-K --safe #-}

module Boolean-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
open import Judgmental
open import Pi-Type

private variable i : Level

data Bool : 𝓤₀ where
  false : Bool
  true : Bool

ind-Bool : {P : Bool → 𝓤 i}
  → P false
  → P true
  → ((x : Bool) → P x)
ind-Bool pf pt false = pf
ind-Bool pf pt true  = pt

comp-Bool-p₀ : {P : Bool → 𝓤 i}
  → (p₀ : P false)
  → (p₁ : P true)
  → ind-Bool {P = P} p₀ p₁ false ≐ p₀
comp-Bool-p₀ = λ p₀ p₁ → equal

comp-Bool-p₁ : {P : Bool → 𝓤 i}
  → (p₀ : P false)
  → (p₁ : P true)
  → ind-Bool {P = P} p₀ p₁ true ≐ p₁
comp-Bool-p₁ = λ p₀ p₁ → equal

neg-Bool : Bool ⇒ Bool
neg-Bool false = true
neg-Bool true = false

{-
_∧_
_∨_
-}


```
