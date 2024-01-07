Empty Type - Φ

```agda
module Empty-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

open import Pi-Type

private variable i : Level

data Φ : 𝓤₀ where

indΦ : {P : Φ → 𝓤 i}
  → Π[ x ⦂ Φ ] P x
indΦ = λ ()

ex-falso : {A : 𝓤 i}
  → Φ ⇒ A
ex-falso = indΦ
