Empty Type - Φ

```agda

{-# OPTIONS --without-K --safe #-}

module Empty where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)

private variable i : Level

-- φ-formaiton Rule
data Φ : 𝓤₀ where

indΦ : {P : Φ → 𝓤 i}
  → (x : Φ) → P x
indΦ = λ ()

ex-falso : {A : 𝓤 i}
  → Φ → A
ex-falso = indΦ

-- Negation
¬_ : 𝓤 i → 𝓤 i
¬ A = A → Φ

is-empty : 𝓤 i → 𝓤 i
is-empty A = A → Φ

¬¬_ : 𝓤 i → 𝓤 i
¬¬ A = ¬ ¬ A

¬¬¬_ : 𝓤 i → 𝓤 i
¬¬¬ A = ¬ ¬ ¬ A

-- Proof of Negation
_ : {P : 𝓤 i} {Q : 𝓤 i}
  → (P → Q) → (¬ Q → ¬ P)
_ = λ p→q ¬q p → ¬q (p→q p)
