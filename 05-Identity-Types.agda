{-# OPTIONS --without-K --safe #-}

module 05-Identity-Types where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)

open import 02-Dependent-Function-Types
open import 03-Natural-Numbers
open import 04-Inductive-Types

private variable 𝓲 𝓳 𝓴 : Level

data _≡_ {A : 𝓤 𝓲} : A → A → 𝓤 𝓲 where
  refl : Π[ a ∶ A ] (a ≡ a)
infix  4 _≡_

_≢_ : {A : 𝓤 𝓲}
  → A → A → 𝓤 𝓲
A ≢ B = ¬ (A ≡ B)
infix  4 _≢_

ind≡ : {A : 𝓤 𝓲} {a : A} {P : Π[ x ∶ A ] Π[ p ∶ a ≡ x ] 𝓤 𝓳}
  → P a (refl a) ⇒ Π[ x ∶ A ] Π[ p ∶ a ≡ x ] (P x p)
ind≡ p a (refl a) = p

concat : {A : 𝓤 𝓲}
  → Π'[ x y z ∶ A ] (x ≡ y ⇒ y ≡ z ⇒ x ≡ z)
concat (refl x) (refl x) = refl x

_∙_ = concat
infixl 7 _∙_

inv : {A : 𝓤 𝓲}
  → Π'[ x y ∶ A ] (x ≡ y ⇒ y ≡ x)
inv (refl x) = refl x

_⁻¹ = inv
infix 40 _⁻¹

assoc : {A : 𝓤 𝓲}
  → Π'[ x y z w ∶ A ] Π[ p ∶ x ≡ y ] Π[ q ∶ y ≡ z ] Π[ r ∶ z ≡ w ]
    ((p ∙ q) ∙ r ≡ p ∙ (q ∙ r))
assoc (refl x) (refl x) (refl x) = refl (refl x)

left-unit : {A : 𝓤 𝓲}
  → Π'[ x y ∶ A ] Π[ p ∶ x ≡ y ] (refl x ∙ p ≡ p)
left-unit (refl x) = refl (refl x)

right-unit : {A : 𝓤 𝓲}
  → Π'[ x y ∶ A ] Π[ p ∶ x ≡ y ] (p ∙ refl y ≡ p)
right-unit (refl x) = refl (refl x)

left-inv : {A : 𝓤 𝓲}
  → Π'[ x y ∶ A ] Π[ p ∶ x ≡ y ] (inv p ∙ p ≡ refl y)
left-inv (refl x) = refl (refl x)

right-inv : {A : 𝓤 𝓲}
  → Π'[ x y ∶ A ] Π[ p ∶ x ≡ y ] (p ∙ inv p ≡ refl x)
right-inv (refl x) = refl (refl x)

-- 5.3 The action on 𝓲dentification of functions
ap : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → (f : A ⇒ B)
  → Π'[ x y ∶ A ] (x ≡ y ⇒ f x ≡ f y)
ap f (refl x) = refl (f x)

ap-id : {A : 𝓤 𝓲}
  → Π'[ x y ∶ A ] Π[ p ∶ x ≡ y ] (p ≡ ap (id A) p)
ap-id (refl x) = refl (refl x)

ap-comp : {A : 𝓤 𝓲} {B : 𝓤 𝓳} {C : 𝓤 𝓴}
  → (f : A ⇒ B)
  → (g : B ⇒ C)
  → Π'[ x y ∶ A ] Π[ p ∶ x ≡ y ] (ap g (ap f p) ≡ ap (g ∘ f) p)
ap-comp f g (refl x) = refl (refl (g (f x)))

ap-refl : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → (f : A ⇒ B)
  → Π[ x ∶ A ] (ap f (refl x) ≡ refl (f x))
ap-refl f x = refl (refl (f x))

ap-inv : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → (f : A ⇒ B)
  → Π'[ x y ∶ A ] Π[ p ∶ x ≡ y ] (ap f (inv p) ≡ inv (ap f p))
ap-inv f (refl x) = refl (ap f (refl x))

ap-concat : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → (f : A ⇒ B)
  → Π'[ x y z ∶ A ] Π[ p ∶ x ≡ y ] Π[ q ∶ y ≡ z ]
    (ap f (p ∙ q) ≡ ap f p ∙ ap f q)
ap-concat f (refl x) (refl x) = refl (ap f (refl x))

-- 5.4 Transport
tr : {A : 𝓤 𝓲}
  → (B : A → 𝓤 𝓳)
  → Π'[ x y ∶ A ] (x ≡ y ⇒ B x ⇒ B y)
tr B (refl x) = id (B x)

apd : {A : 𝓤 𝓲} {B : A → 𝓤 𝓳}
  → (f : Π[ a ∶ A ] B a)
  → Π'[ x y ∶ A ] Π[ p ∶ x ≡ y ] (tr B p (f x) ≡ f y)
apd f (refl x) = refl (f x)

--5.5 The uniqueness of refl

unique-refl : {A : 𝓤 𝓲}
  → (a : A)
  → (y : Σ[ x ∶ A ] (a ≡ x))
  → (a , refl a) ≡ y
unique-refl a (a , refl a) = refl (a , refl a)

--5.6 The laws of addition on ℕ
left-unit-law-addℕ : 
  Π[ n ∶ ℕ ] (0 + n ≡ n)
left-unit-law-addℕ 0ℕ = refl 0ℕ
left-unit-law-addℕ (succℕ n) = ap succℕ (left-unit-law-addℕ n)

right-unit-law-addℕ :
  Π[ n ∶ ℕ ] (n + 0 ≡ n)
right-unit-law-addℕ n = refl n

left-successor-law-addℕ :
  Π[ m n ∶ ℕ ] (succℕ m + n ≡ succℕ (m + n))
left-successor-law-addℕ m 0ℕ = refl (succℕ m)
left-successor-law-addℕ m (succℕ n) = ap succℕ (left-successor-law-addℕ m n)

right-successor-law-addℕ :
  Π[ m n ∶ ℕ ] (m + succℕ n ≡ succℕ (m + n))
right-successor-law-addℕ m n = refl (succℕ (m + n))

associative-addℕ :
  Π[ m n 𝓴 ∶ ℕ ] ((m + n) + 𝓴 ≡ m + (n + 𝓴))
associative-addℕ m n 0ℕ = refl (addℕ m n)
associative-addℕ m n (succℕ 𝓴) = ap succℕ (associative-addℕ m n 𝓴)

commutative-addℕ :
  Π[ m n ∶ ℕ ] (m + n ≡ n + m)
commutative-addℕ 0ℕ n = left-unit-law-addℕ n
commutative-addℕ (succℕ m) n = left-successor-law-addℕ m n ∙ ap succℕ (commutative-addℕ m n)

distributive-inv-concat : {A : 𝓤 𝓲}
  → Π'[ x y z ∶ A ] Π[ p ∶ x ≡ y ] Π[ q ∶ y ≡ z ]
    ((p ∙ q) ⁻¹ ≡ (q ⁻¹) ∙ (p ⁻¹))
distributive-inv-concat (refl x) (refl x) = refl (refl x)

inv-con : {A : 𝓤 𝓲}
  → Π'[ x y z ∶ A ] Π[ p ∶ x ≡ y ] Π[ q ∶ y ≡ z ] Π[ r ∶ x ≡ z ] ((p ∙ q ≡ r) ⇒ (q ≡ p ⁻¹ ∙ r))
inv-con (refl x) (refl x) (refl x) (refl (refl x)) =
  refl (refl x)

lift : {A : 𝓤 𝓲}
  → (B : A → 𝓤 𝓳)
  → Π'[ a x ∶ A ] Π[ p ∶ a ≡ x ] Π[ b ∶ B a ]
    ((a , b) ≡ (x , tr B p b))
lift B (refl a) b = refl (a , b)

Mac-Lane-pentagon : {A : 𝓤 𝓲} →
  Π'[ a b c d e ∶ A ]
  Π[ p ∶ a ≡ b ] Π[ q ∶ b ≡ c ] Π[ r ∶ c ≡ d ] Π[ s ∶ d ≡ e ]
  let α₁ = (ap (λ t → t ∙ s) (assoc p q r))
      α₂ = (assoc p (q ∙ r) s)
      α₃ = (ap (λ t → p ∙ t) (assoc q r s))
      α₄ = (assoc (p ∙ q) r s)
      α₅ = (assoc p q (r ∙ s))
  in ((α₁ ∙ α₂) ∙ α₃) ≡ (α₄ ∙ α₅)
Mac-Lane-pentagon (refl x) (refl x) (refl x) (refl x) = refl (refl (refl x))

left-unit-law-mulℕ :
  Π[ m ∶ ℕ ] (0ℕ * m ≡ 0ℕ)
left-unit-law-mulℕ m = refl 0ℕ

right-unit-law-mulℕ :
  Π[ m ∶ ℕ ] (m * 0ℕ ≡ 0ℕ)
right-unit-law-mulℕ 0ℕ = refl 0ℕ
right-unit-law-mulℕ (succℕ m) = right-unit-law-mulℕ m

left-id-law-mulℕ :
  Π[ m ∶ ℕ ] (1 * m ≡ m)
left-id-law-mulℕ 0ℕ = refl 0ℕ
left-id-law-mulℕ (succℕ m) = ap succℕ (left-id-law-mulℕ m)

right-id-law-mulℕ :
  Π[ m ∶ ℕ ] (m * 1 ≡ m)
right-id-law-mulℕ 0ℕ = refl 0ℕ
right-id-law-mulℕ (succℕ m) = ap succℕ (right-id-law-mulℕ m)

left-succℕ-law-mulℕ :
  Π[ m n ∶ ℕ ] (succℕ m * n ≡ m * n + n)
left-succℕ-law-mulℕ m n = refl (addℕ (mulℕ m n) n)

right-succℕ-law-mulℕ :
  Π[ m n ∶ ℕ ] (m * succℕ n ≡ m + m * n)
right-succℕ-law-mulℕ 0ℕ n = refl 0ℕ
right-succℕ-law-mulℕ (succℕ m) n
  = ap (λ t → succℕ (t + n)) (right-succℕ-law-mulℕ m n)
  ∙ ap succℕ (associative-addℕ m (m * n) n)
  ∙ inv (left-successor-law-addℕ m ((m * n) + n))

commutative-law-mulℕ :
  Π[ m n ∶ ℕ ] (m * n ≡ n * m)
commutative-law-mulℕ 0ℕ n = inv (right-unit-law-mulℕ n)
commutative-law-mulℕ (succℕ m) n
  = (commutative-addℕ (m * n) n)
  ∙ ap (n +_) (commutative-law-mulℕ m n)
  ∙ inv (right-succℕ-law-mulℕ n m)
