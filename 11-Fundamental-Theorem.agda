module 11-Fundamental-Theorem where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import 10-Contractible-Types public

private variable 𝓲 𝓳 𝓴 : Level

tot : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳} {C : A → 𝓤 𝓴}
  → Π[ f ∶ Π[ x ∶ A ] (B x ⇒ C x) ]
    (Σ[ x ∶ A ] B x ⇒ Σ[ x ∶ A ] C x)
tot f (x , y) = (x , f x y)
