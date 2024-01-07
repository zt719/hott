Empty Type - Φ

```agda
module Empty-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

data Φ : 𝓤₀ where
