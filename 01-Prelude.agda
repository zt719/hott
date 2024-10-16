module 01-Prelude where

open import Agda.Primitive public
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to UU)

variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level
