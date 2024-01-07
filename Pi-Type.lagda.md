Depdendent Function Type - Π Type

```
module Pi-Type where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

private variable i j k : Level

Π : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Π A B = (x : A) → B x
syntax Π A (λ x → b) = Π[ x ⦂ A ] b

_⇒_ : 𝓤 i → 𝓤 j → 𝓤 (i ⊔ j)
A ⇒ B = Π[ x ⦂ A ] B
infixr  0 _⇒_

id : (A : 𝓤 i)
  → A ⇒ A
id A = λ x → x

comp : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k}
  → (B ⇒ C)
  → (A ⇒ B)
  → (A ⇒ C)
comp = λ g f x → g (f x)

_∘_ = comp
infix 9 _∘_

const : {A : 𝓤 i} {B : 𝓤 j}
  → B
  → (A ⇒ B)
const y = λ _ → y

σ : {A : 𝓤 i} {B : 𝓤 j} {C : A → B → 𝓤 k}
  → Π[ x ⦂ A ] Π[ y ⦂ B ] C x y
  → Π[ y ⦂ B ] Π[ x ⦂ A ] C x y
σ = λ f x y → f y x
