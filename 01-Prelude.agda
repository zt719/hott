module 01-Prelude where

open import Agda.Primitive public
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to UU)

variable l₁ l₂ l₃ l₄ l₅ l₆ : Level
