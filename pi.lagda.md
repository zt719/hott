```
{-# OPTIONS --without-K --safe #-}

module Pi where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import Agda.Builtin.Equality
  renaming (_≡_ to _≐_; refl to equal)

private variable i j k : Level

```
Dependent Function Type:
  Given type A and type family B on A,
  Π[ x ⦂ A] B x

```agda
Π : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Π A B = (x : A) → B x
syntax Π A (λ x → b) = Π[ x ⦂ A ] b

Π2 : (A : 𝓤 i) (B : A → A → 𝓤 j) → 𝓤 (i ⊔ j)
Π2 A B = (x y : A) → B x y
syntax Π2 A (λ x y → b) = Π[ x , y ⦂ A ] b

Π3 : (A : 𝓤 i) (B : A → A → A → 𝓤 j) → 𝓤 (i ⊔ j)
Π3 A B = (x y z : A) → B x y z
syntax Π3 A (λ x y z → b) = Π[ x , y , z ⦂ A ] b

Π' : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Π' A B = {x : A} → B x
syntax Π' A (λ x → b) = Π'[ x ⦂ A ] b

Π2' : (A : 𝓤 i) (B : A → A → 𝓤 j) → 𝓤 (i ⊔ j)
Π2' A B = {x y : A} → B x y
syntax Π2' A (λ x y → b) = Π'[ x , y ⦂ A ] b

Π3' : (A : 𝓤 i) (B : A → A → A → 𝓤 j) → 𝓤 (i ⊔ j)
Π3' A B = {x y z : A} → B x y z
syntax Π3' A (λ x y z → b) = Π'[ x , y , z ⦂ A ] b

Π4' : (A : 𝓤 i) (B : A → A → A → A → 𝓤 j) → 𝓤 (i ⊔ j)
Π4' A B = {x y z w : A} → B x y z w
syntax Π4' A (λ x y z w → b) = Π'[ x , y , z , w ⦂ A ] b

-- Π-introduction rule
λ-rule : {A : 𝓤 i} {B : A → 𝓤 j}
  → (b : (x : A) → B x)
  → Π[ x ⦂ A ] B x
λ-rule b = λ x → b x

λ-eq : {A : 𝓤 i} {B : A → 𝓤 j}
  → {b b′ : (x : A) → B x}
  → b ≐ b′
  → (λ x → b x) ≐ (λ x → b′ x)
λ-eq equal = equal

-- Π-elimination rule
ev : {A : 𝓤 i} {B : A → 𝓤 j}
  → (f : Π[ x ⦂ A ] B x)
  → (x : A)
  → B x
ev f x = f x

ev-eq : {A : 𝓤 i} {B : A → 𝓤 j}
  → {f f′ : Π[ x ⦂ A ] B x}
  → f ≐ f′
  → (x : A)
  → f x ≐ f′ x
ev-eq equal x = equal

-- Π-computation rules
β-rule : {A : 𝓤 i} {B : A → 𝓤 j}
  → (b : (x : A) → B x)
  → (x : A)
  → (λ y → b y) x ≐ b x
β-rule b x = equal

η-rule : {A : 𝓤 i} {B : A → 𝓤 j}
  → (f : Π[ x ⦂ A ] B x)
  → (λ x → f x) ≐ f
η-rule f = equal
 

```
Ordinary Function Type:
  When type family B is constant

```agda
_⇒_ : 𝓤 i → 𝓤 j → 𝓤 (i ⊔ j)
A ⇒ B = Π[ x ⦂ A ] B
infixr  0 _⇒_

_ : {A : 𝓤 i} {B : 𝓤 j}
  → (A ⇒ B) ≐ Π[ x ⦂ A ] B
_ = equal

λ-rule-⇒ : {A : 𝓤 i} {B : 𝓤 j}
  → (b : (x : A) → B)
  → A ⇒ B
λ-rule-⇒ b = λ x → b x

ev-⇒ : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → (x : A)
  → B
ev-⇒ f x = f x

β-rule-⇒ : {A : 𝓤 i} {B : 𝓤 j}
  → (b : (x : A) → B)
  → (x : A)
  → (λ y → b y) x ≐ b x
β-rule-⇒ b x = equal

η-rule-⇒ : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → (λ x → f x) ≐ f
η-rule-⇒ f = equal

id : (A : 𝓤 i)
  → A ⇒ A
id A = λ x → x

_ : {A : 𝓤 i}
  → id A ≐ (λ x → x)
_ = equal

comp : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k}
  → (B ⇒ C)
  → (A ⇒ B)
  → (A ⇒ C)
comp = λ g f x → g (f x)

_∘_ = comp
infixr 9 _∘_

∘-left-unit : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → id B ∘ f ≐ f
∘-left-unit f = equal

∘-right-unit : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → f ∘ id A ≐ f
∘-right-unit f = equal

const : {A : 𝓤 i} {B : 𝓤 j}
  → B
  → (A → B)
const y = λ _ → y

_ : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k}
  → (f : A ⇒ B)
  → (z : C)
  → const z ∘ f ≐ const z
_ = λ f z → equal

_ : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k}
  → (g : B ⇒ C)
  → (y : B)
  → g ∘ const {A = A} y ≐ const {A = A} (g y)
_ = λ g y → equal

σ : {A : 𝓤 i} {B : 𝓤 j} {C : A → B → 𝓤 k}
  → Π[ x ⦂ A ] Π[ y ⦂ B ] C x y
  → Π[ y ⦂ B ] Π[ x ⦂ A ] C x y
σ = λ f x y → f y x

_ : {A : 𝓤 i} {B : 𝓤 j} {C : A → B → 𝓤 k}
  → σ {A = A} {B = B} {C = C} ∘ σ ≐ id ((x : B) (y : A) → C y x)
_ = equal
