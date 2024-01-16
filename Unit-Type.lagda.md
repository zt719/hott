Unit Type - 𝟙

```agda

{-# OPTIONS --without-K --safe #-}

module Unit-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
open import Judgmental
open import Pi-Type

private variable i : Level

-- 𝟙-formation Rule
data 𝟙 : 𝓤₀ where
  * : 𝟙

ind𝟙 : {P : 𝟙 → 𝓤 i}
  → P * ⇒ Π[ x ⦂ 𝟙 ] P x
ind𝟙 p * = p

comp𝟙 : {P : 𝟙 → 𝓤 i}
  → (p* : P *)
  → ind𝟙 {P = P} p* * ≐ p*
comp𝟙 = λ p* → equal

```
