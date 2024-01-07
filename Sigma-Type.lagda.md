Sigma Type

```agda
module Sigma-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

open import Pi-Type

private variable i j k : Level

data Σ (A : 𝓤 i) (B : A → 𝓤 j) : 𝓤 (i ⊔ j) where
  _,_ : Π[ x ⦂ A ] (B x ⇒ Σ A B)

Sigma : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Sigma A B = Σ A B

syntax Σ A (λ x → b) = Σ[ x ⦂ A ] b

pr₁ : {A : 𝓤 i} {B : A → 𝓤 j}
  → Σ[ x ⦂ A ] B x ⇒ A
pr₁ (x , y) = x

pr₂ : {A : 𝓤 i} {B : A → 𝓤 j}
  → Π[ p ⦂ Σ[ x ⦂ A ] B x ] B (pr₁ p)
pr₂ (x , y) = y

_×_ : (A : 𝓤 i) (B : 𝓤 j) → 𝓤 (i ⊔ j)
A × B = Σ[ x ⦂ A ] B
infix  2 _×_
