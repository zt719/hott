Unit Type - 𝟙

```agda

{-# OPTIONS --without-K --safe #-}

module Unit where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
                           
open import Pi

-- 𝟙-formation Rule
data 𝟙 : 𝓤₀ where
  ＊ : 𝟙

ind𝟙 : {𝓲 : Level} {P : 𝟙 → 𝓤 𝓲}
  → P ＊
  → Π[ x ∶ 𝟙 ] P x
ind𝟙 p ＊ = p

```
