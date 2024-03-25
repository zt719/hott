```agda

{-# OPTIONS --without-K --safe #-}

module Boolean where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import Agda.Builtin.Equality
  renaming (_≡_ to _≐_; refl to equal)

private variable i : Level

open import Pi

data Bool : 𝓤₀ where
  false : Bool
  true : Bool

ind-Bool : {P : Bool → 𝓤 i}
  → P false
  → P true
  → Π[ x ∶ Bool ] P x
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

neg-bool : Bool → Bool
neg-bool false = true
neg-bool true = false



{-
_∧_
_∨_
-}


```
