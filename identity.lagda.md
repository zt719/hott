Identity Type - ≡

```agda

{-# OPTIONS --without-K --safe #-}

module Identity where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)

open import Pi
open import Sigma
open import Naturals

private variable i j k : Level

data _≡_ {A : 𝓤 i} : A → A → 𝓤 i where
  refl : Π[ a ⦂ A ] (a ≡ a)
infix  4 _≡_

ind≡ : {A : 𝓤 i} {a : A} {P : (x : A) (p : a ≡ x) → 𝓤 j}
  → P a (refl a) ⇒ Π[ x ⦂ A ] Π[ p ⦂ a ≡ x ] (P x p)
ind≡ p a (refl a) = p

concat : {A : 𝓤 i}
  → Π'[ x , y , z ⦂ A ] (x ≡ y ⇒ y ≡ z ⇒ x ≡ z)
concat {x = x} {y = y} {z = z} (refl x) (refl x) = refl x

concat′ : {A : 𝓤 i} 
  → Π'[ x , y , z ⦂ A ] (x ≡ y ⇒ y ≡ z ⇒ x ≡ z)
concat′ {x = x} {y = y} {z = z} p q = f x y p z q
  where
    f : {A : 𝓤 i }
      → Π[ x , y ⦂ A ] (x ≡ y ⇒ Π[ z ⦂ A ] (y ≡ z ⇒ x ≡ z))
    f x = ind≡ (λ z → id (x ≡ z))
    
_∙_ = concat
infixl 7 _∙_

inv : {A : 𝓤 i}
  → Π'[ x , y ⦂ A ] (x ≡ y ⇒ y ≡ x)
inv (refl x) = refl x

_⁻¹ = inv
infix 40 _⁻¹

assoc : {A : 𝓤 i}
  → Π'[ x , y , z , w ⦂ A ] Π[ p ⦂ x ≡ y ] Π[ q ⦂ y ≡ z ] Π[ r ⦂ z ≡ w ]
    ((p ∙ q) ∙ r ≡ p ∙ (q ∙ r))
assoc {x = x} {y = y} (refl x) (refl x) (refl x) = refl (refl x)

left-unit : {A : 𝓤 i}
  → Π'[ x , y ⦂ A ] Π[ p ⦂ x ≡ y ] (refl x ∙ p ≡ p)
left-unit (refl x) = refl (refl x)

right-unit : {A : 𝓤 i}
  → Π'[ x , y ⦂ A ] Π[ p ⦂ x ≡ y ] (p ∙ refl y ≡ p)
right-unit (refl x) = refl (refl x)

left-inv : {A : 𝓤 i}
  → Π'[ x , y ⦂ A ] Π[ p ⦂ x ≡ y ] (inv p ∙ p ≡ refl y)
left-inv (refl x) = refl (refl x)

right-inv : {A : 𝓤 i}
  → Π'[ x , y ⦂ A ] Π[ p ⦂ x ≡ y ] (p ∙ inv p ≡ refl x)
right-inv (refl x) = refl (refl x)

-- 5.3 The action on identification of functions
ap : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → Π'[ x , y ⦂ A ] (x ≡ y ⇒ f x ≡ f y)
ap f (refl x) = refl (f x)

ap-id : {A : 𝓤 i}
  → Π'[ x , y ⦂ A ] Π[ p ⦂ x ≡ y ] (p ≡ ap (id A) p)
ap-id (refl x) = refl (refl x)

ap-comp : {A : 𝓤 i} {B : 𝓤 j} {C : 𝓤 k}
  → (f : A ⇒ B)
  → (g : B ⇒ C)
  → Π'[ x , y ⦂ A ] Π[ p ⦂ x ≡ y ] (ap g (ap f p) ≡ ap (g ∘ f) p)
ap-comp f g (refl x) = refl (refl (g (f x)))

ap-refl : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → Π[ x ⦂ A ] (ap f (refl x) ≡ refl (f x))
ap-refl f x = refl (refl (f x))

ap-inv : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → Π'[ x , y ⦂ A ] Π[ p ⦂ x ≡ y ] (ap f (inv p) ≡ inv (ap f p))
ap-inv f (refl x) = refl (ap f (refl x))

ap-concat : {A : 𝓤 i} {B : 𝓤 j}
  → (f : A ⇒ B)
  → Π'[ x , y , z ⦂ A ] Π[ p ⦂ x ≡ y ] Π[ q ⦂ y ≡ z ]
    (ap f (p ∙ q) ≡ ap f p ∙ ap f q)
ap-concat f (refl x) (refl x) = refl (ap f (refl x))

-- 5.4 Transport
tr : {A : 𝓤 i}
  → (B : A → 𝓤 j)
  → Π'[ x , y ⦂ A ] (x ≡ y ⇒ B x ⇒ B y)
tr B (refl x) = id (B x)

apd : {A : 𝓤 i} {B : A → 𝓤 j}
  → (f : Π[ a ⦂ A ] B a)
  → Π'[ x , y ⦂ A ] Π[ p ⦂ x ≡ y ] (tr B p (f x) ≡ f y)
apd f (refl x) = refl (f x)

--5.5 The uniqueness of refl

prop551 : {A : 𝓤 i}
  → (a : A)
  → (y : Σ[ x ⦂ A ] (a ≡ x))
  → Σ[ p ⦂  Σ[ x ⦂ A ] (a ≡ x) ] (p ≡ y)
prop551 a (a , refl a) = (a , refl a) , refl (a , refl a)

--5.6 The laws of addition on ℕ
left-unit-law-addℕ : 
  Π[ n ⦂ ℕ ] (0 + n ≡ n)
left-unit-law-addℕ = indℕ (refl 0ℕ) (λ _ p → ap succℕ p)

right-unit-law-addℕ :
  Π[ n ⦂ ℕ ] (n + 0 ≡ n)
right-unit-law-addℕ n = refl n

left-successor-law-addℕ :
  Π[ m , n ⦂ ℕ ] (succℕ m + n ≡ succℕ (m + n))
left-successor-law-addℕ m =
  indℕ (refl (succℕ m)) (λ _ p → ap succℕ p)

right-successor-law-addℕ :
  Π[ m , n ⦂ ℕ ] (m + succℕ n ≡ succℕ (m + n))
right-successor-law-addℕ m n = refl (succℕ (m + n))

associative-addℕ :
  Π[ m , n , k ⦂ ℕ ] ((m + n) + k ≡ m + (n + k))
associative-addℕ m n =
  indℕ (refl (m + n)) (λ _ p → ap succℕ p)

commutative-addℕ :
  Π[ m , n ⦂ ℕ ] (m + n ≡ n + m)
commutative-addℕ m =
  indℕ
    (right-unit-law-addℕ m ∙ (left-unit-law-addℕ m ⁻¹))
    (λ n p → ap succℕ p ∙ (left-successor-law-addℕ n m ⁻¹))

distributive-inv-concat : {A : 𝓤 i}
  → Π'[ x , y , z ⦂ A ] Π[ p ⦂ x ≡ y ] Π[ q ⦂ y ≡ z ]
    ((p ∙ q) ⁻¹ ≡ (q ⁻¹) ∙ (p ⁻¹))
distributive-inv-concat (refl x) (refl x) = refl (refl x)

inv-con : {A : 𝓤 i}
  → Π'[ x , y , z ⦂ A ] Π[ p ⦂ x ≡ y ] Π[ q ⦂ y ≡ z ] Π[ r ⦂ x ≡ z ] ((p ∙ q ≡ r) ⇒ (q ≡ p ⁻¹ ∙ r))
inv-con (refl x) (refl x) (refl x) (refl (refl x)) =
  refl (refl x)
```
