Empty Type - Φ

```agda

{-# OPTIONS --without-K --safe #-}

module Empty where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)

private variable 𝓲 : Level

-- φ-formaiton Rule
data Φ : 𝓤₀ where

indΦ : {P : Φ → 𝓤 𝓲}
  → (x : Φ) → P x
indΦ = λ ()

ex-falso : {A : 𝓤 𝓲}
  → Φ → A
ex-falso = indΦ

-- Negation
¬_ : 𝓤 𝓲 → 𝓤 𝓲
¬ A = A → Φ

is-empty : 𝓤 𝓲 → 𝓤 𝓲 
is-empty A = A → Φ

¬¬_ : 𝓤 𝓲 → 𝓤 𝓲 
¬¬ A = ¬ ¬ A

¬¬¬_ : 𝓤 𝓲 → 𝓤 𝓲 
¬¬¬ A = ¬ ¬ ¬ A

-- Proof of Negation
_ : {P : 𝓤 𝓲 } {Q : 𝓤 𝓲}
  → (P → Q) → (¬ Q → ¬ P)
_ = λ p→q ¬q p → ¬q (p→q p)
