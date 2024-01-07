Some scratch from ⟨ Introduction to Homotopy Type Theory >

```
module HoTT where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

open import Pi-Type
open import Natural-Type
open import Unit-Type
open import Coproduct-Type
open import Sigma-Type
open import Identity-Type

variable i j k l : Level
```

Jugemental Equality

```
data _≐_ {A : 𝓤 i} (x : A) : A → 𝓤 i where
  equal : x ≐ x
infix 4 _≐_

postulate
  ext : {A : 𝓤 i} {B : A → 𝓤 j} {f g : (x : A) → B x}
    → ((x : A) → f x ≐ g x)
      -------------------
    → (λ x → f x) ≐ (λ x → g x)

ƛ : {A : 𝓤 i} {B : A → 𝓤 j}
  → ((x : A) → B x)
    ---------------
  → Π[ x ⦂ A ] B x
ƛ b = λ x → b x

ƛ-eq : {A : 𝓤 i} {B : A → 𝓤 j} {b b′ : (x : A) → B x}
  → ((x : A) → b x ≐ b′ x)
    --------------------------
  → (λ x → b x) ≐ (λ x → b′ x)
ƛ-eq = ext

ev : {A : 𝓤 i} {B : A → 𝓤 j}
  → (f : Π[ x ⦂ A ] B x)
    -------------------
  → (x : A) → B x
ev f x = f x

ev-eq : {A : 𝓤 i} {B : A → 𝓤 j} {f f′ : Π[ x ⦂ A ] B x}
  → f ≐ f′
    --------------------
  → (x : A) → f x ≐ f′ x
ev-eq equal x = equal

β : {A : 𝓤 i} {B : A → 𝓤 j}
  → (b : (x : A) → B x)
    -----------------------------
  → (x : A) → (λ y → b y) x ≐ b x
β b x = equal

η : {A : 𝓤 i} {B : A → 𝓤 j}
  → (f : Π[ x ⦂ A ] B x)
    --------------------
  → (λ x → f x) ≐ f
η = λ f → equal

ƛ-f : {A : 𝓤 i} {B : 𝓤 j}
  → ((x : A) → B)
    -------------
  → A ⇒ B
ƛ-f = ƛ

ev-f : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
    -----------
  → (x : A) → B
ev-f = ev

β-f : {A : 𝓤 i} {B : 𝓤 j}
  → (b : (x : A) → B)
    -----------------------------
  → (x : A) → (λ y → b y) x ≐ b x
β-f = β

η-f : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
    ---------------
  → (λ x → f x) ≐ f
η-f = η

_ : {A : 𝓤 i}
  → id A ≐ (λ x → x)
_ = equal

_ : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 j} {D : 𝓤 l}
  → (f : A ⇒ B)
  → (g : B ⇒ C)
  → (h : C ⇒ D)
  → (h ∘ g) ∘ f ≐ h ∘ (g ∘ f)
_ = λ f g h → equal

_ : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → id B ∘ f ≐ f
_ = λ f → equal

_ : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → f ∘ id A ≐ f
_ = λ f → equal

ℕ-ind : {P : ℕ → 𝓤 i}
  → P 0ℕ
  → Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n))
    ------------------------------
  → Π[ n ⦂ ℕ ] P n
ℕ-ind p₀ pₛ 0ℕ = p₀
ℕ-ind p₀ pₛ (succℕ n) = pₛ n (ℕ-ind p₀ pₛ n)

indℕ : {P : ℕ → 𝓤 i}
  → P 0ℕ ⇒ Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)) ⇒ Π[ n ⦂ ℕ ] P n
indℕ = ℕ-ind

ℕ-comp-p₀ : {P : ℕ → 𝓤 i}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)))
    -------------------------------------
  → indℕ p₀ pₛ 0ℕ ≐ p₀
ℕ-comp-p₀ p₀ pₛ = equal

ℕ-comp-pₛ : {P : ℕ → 𝓤 i}
  → (p₀ : P 0ℕ)
  → (pₛ : Π[ n ⦂ ℕ ] (P n ⇒ P (succℕ n)))
    ----------------------------------------------------
  → (n : ℕ) → indℕ p₀ pₛ (succℕ n) ≐ pₛ n (indℕ p₀ pₛ n)
ℕ-comp-pₛ p₀ pₛ n = equal

𝟙-comp : {P : 𝟙 → 𝓤 i}
  → (p* : P *)
  → ind𝟙 {i} {P} p* * ≐ p*
𝟙-comp = λ p* → equal

ind∔ : {A : 𝓤 i} {B : 𝓤 j} {P : A ∔ B → 𝓤 k}
  → Π[ x ⦂ A ] P (inl x) ⇒ Π[ y ⦂ B ] P (inr y) ⇒ Π[ z ⦂ A ∔ B ] P z
ind∔ f g (inl x) = f x
ind∔ f g (inr y) = g y

indΣ : {A : 𝓤 i} {B : A → 𝓤 j} {P : Σ[ x ⦂ A ] B x → 𝓤 k}
  → Π[ x ⦂ A ] Π[ y ⦂ B x ] P (x , y) ⇒ Π[ z ⦂ Σ[ x ⦂ A ] B x ] P z
indΣ f (x , y) = f x y

curry = indΣ

ev-pair : {A : 𝓤 i} {B : A → 𝓤 j} {P : Σ[ x ⦂ A ] B x → 𝓤 k}
  → Π[ z ⦂ Σ[ x ⦂ A ] B x ] P z ⇒ Π[ x ⦂ A ] Π[ y ⦂ B x ] P (x , y)
ev-pair f x y = f (x , y)

uncurry = ev-pair

ind× : {A : 𝓤 i} {B : 𝓤 j} {P : A × B → 𝓤 k}
  → Π[ x ⦂ A ] Π[ y ⦂ B ] P (x , y) ⇒ Π[ z ⦂ A × B ] P z
ind× f (x , y) = f x y

ind-eqₐ : {A : 𝓤 i} {a : A} {P : (x : A) → a ≡ x → 𝓤 j}
  → P a (refl a) ⇒ Π[ x ⦂ A ] Π[ p ⦂ a ≡ x ] P x p
ind-eqₐ p a (refl a) = p

≡-intro : {A : 𝓤 i}
  → (a : A)
    -------
  → a ≡ a
≡-intro a = refl a

≡-elim : {A : 𝓤 i} 
  → (a : A)
  → (P : (x : A) (p : a ≡ x) → 𝓤 j)
    ----------------------------------------------
  → P a (refl a) ⇒ Π[ x ⦂ A ] Π[ p ⦂ a ≡ x ] P x p
≡-elim a P = ind-eqₐ

≡-comp : {A : 𝓤 i}
  → (a : A)
  → (P : (x : A) (p : a ≡ x) → 𝓤 j)
    --------------------------------
  → (u : P a (refl a))
  → ind-eqₐ {i} {j} {A} {a} {λ a a≡x → P a a≡x} u a (refl a) ≐ u
≡-comp = λ a P u → equal

assoc-≡ : {A : 𝓤 i} {x y z w : A}
  → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc-≡ (refl x) (refl x) (refl x) = refl (refl x)

left-unit-≡ : {A : 𝓤 i} {x y : A}
  → (p : x ≡ y)
  → refl x ∙ p ≡ p
left-unit-≡ (refl x) = refl (refl x)

right-unit-≡ : {A : 𝓤 i} {x y : A}
  → (p : x ≡ y)
  → p ∙ refl y ≡ p
right-unit-≡ (refl x) = refl (refl x)

left-inv-≡ : {A : 𝓤 i} {x y : A}
  → (p : x ≡ y)
  → inv p ∙ p ≡ refl y
left-inv-≡ (refl x) = refl (refl x)

right-inv-≡ : {A : 𝓤 i} {x y : A}
  → (p : x ≡ y)
  → p ∙ inv p ≡ refl x
right-inv-≡ (refl x) = refl (refl x)

ap-id : {A : 𝓤 i}
  → {x y : A}
  → (p : x ≡ y)
  → p ≡ ap (id A)  p
ap-id (refl x) = refl (refl x)

ap-comp : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k}
  → (f : A → B)
  → (g : B → C)
  →  {x y : A}
  → (p : x ≡ y)
  → ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp f g (refl x) = refl (refl (g (f x)))

ap-refl : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A → B)
  → (x : A)
  → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-inv : {A : 𝓤 i} {B : 𝓤 j} {x y : A}
  → (f : A → B)
  → (p : x ≡ y)
  → ap f (inv p) ≡ inv (ap f p)
ap-inv {x = x} f (refl .x) = refl (refl (f x))

ap-concat : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k} {x y z : A}
  → (f : A → B)
  → (p : x ≡ y)
  → (q : y ≡ z)
  → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-concat {x = x} f (refl .x) (refl .x) = refl (refl (f x))

apd : {A : 𝓤 i} {B : A → 𝓤 j} {x y : A}
  → (f : (x : A) → B x)
  → (p : x ≡ y)
  → tr B p (f x) ≡ f y
apd f (refl x) = refl (f x)
