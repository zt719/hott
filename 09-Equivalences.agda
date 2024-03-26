module 09-Equivalences where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)

open import 02-Dependent-Function-Types
open import 03-Natural-Numbers
open import 04-Inductive-Types
open import 05-Identity-Types
open import 06-Universes
open import 07-Curry-Howard

private variable 𝓲 𝓳 𝓴 : Level

-- 9.1 Homotopies

_~_ : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π[ f g ∶ Π[ x ∶ A ] B x ] 𝓤 (𝓲 ⊔ 𝓳)
f ~ g = Π[ x ∶ _ ] (f x ≡ g x)
infix  4 _~_

neg-neg-bool : neg-bool ∘ neg-bool ~ id Bool
neg-neg-bool false = refl false
neg-neg-bool true  = refl true

-- homotopies between homotopies
_~~_ : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π'[ f g ∶ Π[ x ∶ A ] B x ] Π[ H K ∶ f ~ g ] 𝓤 (𝓲 ⊔ 𝓳)
H ~~ K = Π[ x ∶ _ ] (H x ≡ K x)

refl-htpy : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → reflexive (λ (f g : Π[ x ∶ A ] B x) → f ~ g)
refl-htpy {x = f} x = refl (f x)

inv-htpy : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → symmetric (λ (f g : Π[ x ∶ A ] B x) → f ~ g)
inv-htpy H x = H x ⁻¹

concat-htpy : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → transitive (λ (f g : Π[ x ∶ A ] B x) → f ~ g)
concat-htpy H K x = H x ∙ K x

_∙h_ = concat-htpy

assoc-htpy : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π'[ f g h i ∶ Π[ x ∶ A ] B x ]
    Π[ H ∶ f ~ g ] Π[ K ∶ g ~ h ] Π[ L ∶ h ~ i ]
    ((H ∙h K) ∙h L ~ H ∙h (K ∙h L))
assoc-htpy H K L x = assoc (H x) (K x) (L x)

left-unit-htpy : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π'[ f g ∶ Π[ x ∶ A ] B x ] Π[ H ∶ f ~ g ] (refl-htpy ∙h H ~ H)
left-unit-htpy {x₁ = f} {x₂ = g} H x = left-unit (H x)

right-unit-htpy : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π'[ f g ∶ Π[ x ∶ A ] B x ] Π[ H ∶ f ~ g ] (H ∙h refl-htpy ~ H)
right-unit-htpy {x₁ = f} {x₂ = g} H x = right-unit (H x)

left-inv-htpy : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π'[ f g ∶ Π[ x ∶ A ] B x ] Π[ H ∶ f ~ g ] (inv-htpy H ∙h H ~ refl-htpy)
left-inv-htpy H x = left-inv (H x)

right-inv-htpy : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π'[ f g ∶ Π[ x ∶ A ] B x ] Π[ H ∶ f ~ g ] (H ∙h inv-htpy H ~ refl-htpy)
right-inv-htpy H x = right-inv (H x)

-- whiskering

left-whisk : {A : 𝓤 𝓲} {B : 𝓤 𝓳} {C : 𝓤 𝓴}
  → Π'[ f g ∶ A ⇒ B ] Π[ h ∶ B ⇒ C ] Π[ H ∶ f ~ g ] (h ∘ f ~ h ∘ g)
left-whisk h H x = ap h (H x)

_∙lw_ = left-whisk

right-whisk : {A : 𝓤 𝓲} {B : 𝓤 𝓳} {C : 𝓤 𝓴}
  → Π'[ g h ∶ B ⇒ C ] Π[ H ∶ g ~ h ] Π[ f ∶ A ⇒ B ] (g ∘ f ~ h ∘ f)
right-whisk H f x = H (f x)

_∙rw_ = right-whisk

-- 9.2 Bi-invertible maps

-- sections
sec : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] 𝓤 (𝓲 ⊔ 𝓳)
sec {A = A} {B = B} f = Σ[ g ∶ B ⇒ A ] (f ∘ g ~ id B)

-- retractions
retr : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] 𝓤 (𝓲 ⊔ 𝓳)
retr {A = A} {B = B} f = Σ[ h ∶ B ⇒ A ] (h ∘ f ~ id A)

-- equivalence
is-equiv : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] 𝓤 (𝓲 ⊔ 𝓳)
is-equiv f = sec f × retr f

_≃_ : 𝓤 𝓲 ⇒ 𝓤 𝓳 ⇒ 𝓤 (𝓲 ⊔ 𝓳)
A ≃ B = Σ[ f ∶ A ⇒ B ] is-equiv f

neg-bool-is-equiv : is-equiv neg-bool
neg-bool-is-equiv
  = (neg-bool , neg-neg-bool) , (neg-bool , neg-neg-bool)

has-inverse : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] 𝓤 (𝓲 ⊔ 𝓳)
has-inverse {A = A} {B = B} f
  = Σ[ g ∶ B ⇒ A ] (f ∘ g ~ id B × g ∘ f ~ id A)

has-inverse⇒is-equiv : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π'[ f ∶ A ⇒ B ] (has-inverse f ⇒ is-equiv f)
has-inverse⇒is-equiv (g , (f∘g~idB , g∘f~idA))
  = (g , f∘g~idB) , (g , g∘f~idA)

is-equiv⇒has-inverse : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] (is-equiv f ⇒ has-inverse f)
is-equiv⇒has-inverse f ((g , G) , (h , H))
  = g , (G , (K ∙rw f) ∙h H)
  where
  K : g ~ h
  K = (inv-htpy (H ∙rw g)) ∙h (h ∙lw G)

{-
Φ∔B≃B : {B : 𝓤 𝓲}
  → Φ ∔ B ≃ B
Φ∔B≃B {B = B} = inr ((id B) , ((id B) , refl) , (id B) , refl)

...
-}

-- 9.3 Characterizing the identity types of Σ-types

EqΣ : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Σ[ x ∶ A ] B x ⇒ Σ[ x ∶ A ] B x ⇒ 𝓤 (𝓲 ⊔ 𝓳)
EqΣ {B = B} s t = Σ[ α ∶ pr₁ s ≡ pr₁ t ] (tr B α (pr₂ s) ≡ pr₂ t)

reflexive-EqΣ : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → Π[ s ∶ Σ[ x ∶ A ] B x ] EqΣ s s
reflexive-EqΣ s = refl (pr₁ s) , refl (pr₂ s)
