module 10-Contractible-Types where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)

open import 02-Dependent-Function-Types
open import 03-Natural-Numbers
open import 04-Inductive-Types
open import 05-Identity-Types
open import 06-Universes
open import 07-Curry-Howard
open import 09-Equivalences

private variable 𝓲 𝓳 𝓴 : Level

-- 10.1 Contractible types

is-contr : Π[ A ∶ 𝓤 𝓲 ] 𝓤 𝓲
is-contr A = Σ[ c ∶ A ] Π[ x ∶ A ] (c ≡ x)

center : {A : 𝓤 𝓲}
  → Π[ a ∶ is-contr A ] A
center (c , C) = c

contraction : {A : 𝓤 𝓲}
  → Π[ a ∶ is-contr A ] (const (center a) ~ id A)
contraction (c , C) = C

Σ-is-contr : {A : 𝓤 𝓲}
  → Π[ a ∶ A ] is-contr (Σ[ x ∶ A ] (a ≡ x))
Σ-is-contr a = ((a , refl a) , prop551 a)

-- 10.2 Singleton induction

ev-pt : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → (a : A)
  → (Π[ x ∶ A ] B x) ⇒ B a
ev-pt A B a f = f a

is-sing : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → (a : A)
  → 𝓤 (𝓲 ⊔ 𝓳)
is-sing A B a = sec (ev-pt A B a)

ind-sing : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → (a : A)
  → (sing : is-sing A B a)
  → B a ⇒ Π[ x ∶ A ] B x
ind-sing A B a (s , is-sec) b x = s b x

comp-sing : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → (a : A)
  → (sing : is-sing A B a)
  → ev-pt A B a ∘ ind-sing A B a sing ~ id (B a)
comp-sing A B a (s , is-sec) = is-sec

𝟙-is-sing : {B : 𝟙 → 𝓤 𝓲}
  → is-sing 𝟙 B ＊
𝟙-is-sing = (ind𝟙 , λ b → refl b)
