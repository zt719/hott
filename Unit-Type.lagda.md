Unit Type

```agda
module Unit-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

open import Pi-Type

private variable i j k l : Level

data 𝟙 : 𝓤₀ where
  * : 𝟙

ind𝟙 : {P : 𝟙 → 𝓤 i}
  → P * ⇒ Π[ x ⦂ 𝟙 ] P x
ind𝟙 p* * = p*

