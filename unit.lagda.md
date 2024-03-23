Unit Type - 𝟙

```agda

{-# OPTIONS --without-K --safe #-}

module Unit where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
                           
private variable i : Level

-- 𝟙-formation Rule
data 𝟙 : 𝓤₀ where
  ＊ : 𝟙

ind𝟙 : {P : 𝟙 → 𝓤 i}
  → P ＊ → (x : 𝟙) → P x
ind𝟙 p ＊ = p
```
