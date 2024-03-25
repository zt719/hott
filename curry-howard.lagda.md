```agda
module Curry-Howard where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import Agda.Builtin.Equality
  renaming (_≡_ to _≐_; refl to equal)

open import Pi
open import Sigma
open import Naturals
open import Empty
open import Coproducts
open import Unit
open import Identity
open import Universes

postulate
  left-distributive-mulℕ : Π[ m n k ∶ ℕ ] (m * (n + k) ≡ m * n + m * k)

-- Curry-Howard Interpretation

_∣_ : Π[ d n ∶ ℕ ] 𝓤₀
d ∣ n = Σ[ k ∶ ℕ ] (d * k ≡ n)

three-divides-six : 3 ∣ 6
three-divides-six = (2 , refl 6)

one-dividesℕ : Π[ x ∶ ℕ ] (1 ∣ x)
one-dividesℕ x = (x , left-id-law-mulℕ x)

-- Proposition 7.1.5

p7-1-5 : Π[ x y d ∶ ℕ ] ((d ∣ x × d ∣ y) ⇒ d ∣ (x + y))
p7-1-5 x y d ((k , d*k≡x) , (l , d*l≡y)) = ((k + l) , α ∙ β ∙ γ)
  where
  α : d * (k + l) ≡ d * k + d * l
  α = left-distributive-mulℕ d k l
  β : d * k + d * l ≡ x + d * l
  β = ap (λ t → t + d * l) d*k≡x
  γ : x + d * l ≡ x + y
  γ = ap (λ t → x + t) d*l≡y


-- Fin

{-
Fin : ℕ → 𝓤₀
Fin 0ℕ = Φ
Fin (succℕ k) = Fin k ∔ 𝟙
-}

-- 7.2 The congruence relations on ℕ

reflexive : {i j : Level} {A : 𝓤 i}
  → (R : A ⇒ A ⇒ 𝓤 j)
  → 𝓤 (i ⊔ j)
reflexive {A = A} R = Π'[ x ∶ A ] R x x

ρ = reflexive

symmetric : {i j : Level} {A : 𝓤 i}
  → (R : A ⇒ A ⇒ 𝓤 j)
  → 𝓤 (i ⊔ j)
symmetric {A = A} R = Π'[ x y ∶ A ] (R x y ⇒ R y x)

δ = symmetric

transitive : {i j : Level} {A : 𝓤 i}
  → (R : A ⇒ A ⇒ 𝓤 j)
  → 𝓤 (i ⊔ j)
transitive {A = A} R = Π'[ x y z ∶ A ] (R x y ⇒ R y z ⇒ R x z)

τ = transitive 

distℕ : ℕ ⇒ ℕ ⇒ ℕ
distℕ 0ℕ 0ℕ = 0ℕ
distℕ 0ℕ (succℕ y) = succℕ y
distℕ (succℕ x) 0ℕ = succℕ x
distℕ (succℕ x) (succℕ y) = distℕ x y

distℕ-refl : Π[ x ∶ ℕ ] (0ℕ ≡ distℕ x x)
distℕ-refl 0ℕ = refl 0ℕ
distℕ-refl (succℕ x) = distℕ-refl x

distℕ-sym : Π[ x y ∶ ℕ ] (distℕ x y ≡ distℕ y x)
distℕ-sym 0ℕ 0ℕ = refl 0ℕ
distℕ-sym 0ℕ (succℕ y) = refl (succℕ y)
distℕ-sym (succℕ x) 0ℕ = refl (succℕ x)
distℕ-sym (succℕ x) (succℕ y) = distℕ-sym x y

_≡_mod_ : ℕ ⇒ ℕ ⇒ ℕ ⇒ 𝓤₀
x ≡ y mod k = k ∣ distℕ x y

mod-reflexive :
  Π[ k ∶ ℕ ] reflexive (_≡_mod k)
mod-reflexive k {x} = 0ℕ , right-unit-law-mulℕ k ∙ distℕ-refl x

mod-sym :
  Π[ k ∶ ℕ ] symmetric (_≡_mod k)
mod-sym k {x} {y} (l , k*l≡distℕxy) = l , k*l≡distℕxy ∙ distℕ-sym x y

{-
mod-trans :
  Π[ k , x , y , z ∶ ℕ ] (x ≡ y mod k ⇒ y ≡ z mod k ⇒ x ≡ z mod k)
mod-trans k x y z = {!!}
-}

data Fin : ℕ → 𝓤₀ where
  ★ : Π'[ k ∶ ℕ ] Fin (succℕ k)
  i : Π'[ k ∶ ℕ ] (Fin k ⇒ Fin (succℕ k))
  
ind-f : {l : Level} {P : Π[ k ∶ ℕ ] Π[ x ∶ Fin k ] 𝓤 l}
  → (g : Π[ k ∶ ℕ ] Π[ x ∶ Fin k ] (P k x ⇒ P (succℕ k) (i x)))
  → (p : Π[ k ∶ ℕ ] (P (succℕ k) ★))
  → Π[ k ∶ ℕ ] Π[ x ∶ Fin k ] P k x
ind-f g p (succℕ k) ★    = p k
ind-f g p (succℕ k) (i x) = g k x (ind-f g p k x)

ι : Π[ k ∶ ℕ ] (Fin k ⇒ ℕ)
ι (succℕ k) ★ = k
ι (succℕ k) (i x) = ι k x


inequalities :
  Π[ k ∶ ℕ ] Π[ x ∶ Fin k ] (ι (succℕ k) (i x) < k)
inequalities (succℕ k) ★ = ine k
inequalities (succℕ k) (i x)
  = <-trans (ι k x) (k) (succℕ k) (inequalities k x) (ine k)

-- ι is injective
{-
α : Π[ k ∶ ℕ ] Π[ x , y ∶ Fin k ] (ι k x ≡ ι k y ⇒ x ≡ y)
α (succℕ k) ★ ★ p = refl ★
α (succℕ k) ★ (i y) p = ex-falso (g p)
  where
  g : ι (succℕ k) ★ ≢ ι (succℕ k) (i y)
  g = {!!}
α (succℕ k) (i x) ★ p = ex-falso (f p)
  where
  f : (ι (succℕ k) (i x) ≡ ι (succℕ k) ★) ⇒ Φ
  f = {!!}
α (succℕ k) (i x) (i y) p = ap i (α k x y p)
-}

Fin' : ℕ → 𝓤₀
Fin' 0ℕ = Φ
Fin' (succℕ k) = Fin' k ∔ 𝟙

★' : Π'[ k ∶ ℕ ] Fin' (succℕ k)
★' = inr ＊

i' : Π'[ k ∶ ℕ ] (Fin' k ⇒ Fin' (succℕ k))
i' = inl

ι' : Π[ k ∶ ℕ ] (Fin' k ⇒ ℕ)
ι' (succℕ k) (inl x) = ι' k x
ι' (succℕ k) (inr ＊) = k

-- 7.4 The natrual numbers modulo k+1

is-split-surjective :
  {i j : Level} {A : 𝓤 i} {B : 𝓤 j}
  → Π[ f ∶ A ⇒ B ] 𝓤 (i ⊔ j)
is-split-surjective {A = A} {B = B} f
  = Π[ b ∶ B ] Σ[ a ∶ A ] (f a ≡ b)

zero : Π[ k ∶ ℕ ] Fin (succℕ k)
zero 0ℕ = ★
zero (succℕ k) = i (zero k)

skip-zero : Π[ k ∶ ℕ ] (Fin k ⇒ Fin (succℕ k))
skip-zero (succℕ k) ★ = ★
skip-zero (succℕ k) (i x) = i (skip-zero k x)

succ : Π[ k ∶ ℕ ] (Fin k ⇒ Fin k)
succ (succℕ k) ★ = zero k
succ (succℕ k) (i x) = skip-zero k x

{-
[_] : ℕ ⇒ Π[ k ∶ ℕ ] Fin (succℕ k)
[ 0ℕ ] k = zero k
[ succℕ x ] k = {!!}
-}

```
