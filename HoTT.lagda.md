Some scratch from ⟨ Introduction to Homotopy Type Theory >

```

{-# OPTIONS --without-K --safe #-}

module HoTT where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)

open import Products
open import Naturals
open import Unit
open import Sums
open import Products
open import Identity
open import Empty

private variable i j k l : Level
```

```agda



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
  → p ≡ ap id p
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

Eqℕ : ℕ → ℕ → 𝓤₀
Eqℕ 0ℕ 0ℕ = 𝟙
Eqℕ 0ℕ (succℕ n) = Φ
Eqℕ (succℕ m) 0ℕ = Φ
Eqℕ (succℕ m) (succℕ n) = Eqℕ m n

E₀ : ℕ → 𝓤₀
E₀ 0ℕ = 𝟙
E₀ (succℕ n) = Φ

Eₛ : ℕ → (ℕ → 𝓤₀) → ℕ → 𝓤₀
Eₛ m X 0ℕ = Φ
Eₛ m X (succℕ n) = X n

E₀≐ : {m : ℕ}
  → Eqℕ 0ℕ m ≐ E₀ m
E₀≐ {0ℕ} = equal
E₀≐ {succℕ m} = equal

Eₛ≐ : {m n : ℕ}
  → Eqℕ (succℕ m) n ≐ Eₛ m (Eqℕ m) n
Eₛ≐ {n = 0ℕ} = equal
Eₛ≐ {n = succℕ m} = equal

refl-Eqℕ : Π[ n ⦂ ℕ ] Eqℕ n n
refl-Eqℕ 0ℕ = *
refl-Eqℕ (succℕ n) = refl-Eqℕ n

_↔_ : 𝓤 i → 𝓤 i → 𝓤 i
A ↔ B = (A → B) × (B → A)

≡↔Eqℕ : {m n : ℕ}
  → (m ≡ n) ↔ Eqℕ m n
≡↔Eqℕ {m} {n} = (λ { (refl .m) → refl-Eqℕ m }) , f
  where
    f : {m n : ℕ} → Eqℕ m n → (m ≡ n)
    f {0ℕ} {0ℕ} = λ * → refl 0ℕ
    f {0ℕ} {succℕ n} = λ ()
    f {succℕ m} {0ℕ} = λ ()
    f {succℕ m} {succℕ n} = id ∘ ap succℕ ∘ f {m} {n}

p7 : {m n : ℕ}
  → (m ≡ n) ↔ (succℕ m ≡ succℕ n)
p7 {m} {n} = (ap succℕ) , (pr₂ ≡↔Eqℕ ∘  pr₁ ≡↔Eqℕ)

_≢_ : {A : 𝓤 i} → A → A → 𝓤 i
x ≢ y = ¬ (x ≡ y)

p8 : {n : ℕ}
  → 0ℕ ≢ succℕ n
p8 {n} = pr₁ (≡↔Eqℕ {n = succℕ n})

e6-1a1 : {m n k : ℕ}
  → (m ≡ n) ↔ (m + k ≡ n + k)
e6-1a1 {m} {n} {k} = (ap (_+ k)) , (pr₂ ≡↔Eqℕ ∘ f {m} {n} {k} ∘ pr₁ ≡↔Eqℕ)
  where
  f : {m n k : ℕ}
    → Eqℕ (m + k) (n + k) → Eqℕ m n
  f {m} {n} {0ℕ} = id
  f {m} {n} {succℕ k} = f {k = k}

{-
e6-1a2 : {m n k : ℕ}
  → (m ≡ n) ↔ (m · succℕ k ≡ n · succℕ k)
e6-1a2 {m} {n} {k} = ap (_· succℕ k) , (pr₂ ≡↔Eqℕ ∘ f {m} {n} {k} ∘ pr₁ ≡↔Eqℕ)
  where
  f : {m n k : ℕ}
    → Eqℕ (m · succℕ k) (n · succℕ k) → Eqℕ m n
  f {m} {n} {0ℕ} = id (Eqℕ m n)
  f {m} {n} {succℕ k} = {!!}
-}

