module 07-Curry-Howard where

open import 06-Universes public

-- 7.1 The Curry-Howard interpretation

_∣_ : (d n : ℕ) → UU₀
d ∣ n = Σ k ∶ ℕ , (d * k ≡ n)

three-divides-six : 3 ∣ 6
three-divides-six = (2 , refl 6)

one-dividesℕ : (x : ℕ) → 1 ∣ x
one-dividesℕ x = (x , *-idˡ x)

-- Proposition 7.1.5

p7-1-5 : (x y d : ℕ)
  → d ∣ x × d ∣ y
  → d ∣ (x + y)
p7-1-5 x y d ((k , d*k≡x) , (l , d*l≡y)) = ((k + l) , α ∙ β ∙ γ)
  where
  α : d * (k + l) ≡ d * k + d * l
  α = *-+-distrˡ d k l
  β : d * k + d * l ≡ x + d * l
  β = ap (_+ d * l) d*k≡x
  γ : x + d * l ≡ x + y
  γ = ap (x +_) d*l≡y

-- 7.2 The congruence relations on ℕ

distℕ : ℕ → ℕ → ℕ
distℕ 0ℕ 0ℕ = 0ℕ
distℕ 0ℕ (succℕ y) = succℕ y
distℕ (succℕ x) 0ℕ = succℕ x
distℕ (succℕ x) (succℕ y) = distℕ x y

distℕ-refl : (x : ℕ) → 0ℕ ≡ distℕ x x
distℕ-refl 0ℕ = refl 0ℕ
distℕ-refl (succℕ x) = distℕ-refl x

distℕ-sym : (x y : ℕ) → distℕ x y ≡ distℕ y x
distℕ-sym 0ℕ 0ℕ = refl 0ℕ
distℕ-sym 0ℕ (succℕ y) = refl (succℕ y)
distℕ-sym (succℕ x) 0ℕ = refl (succℕ x)
distℕ-sym (succℕ x) (succℕ y) = distℕ-sym x y

_≡_mod_ : ℕ → ℕ → ℕ → UU₀
x ≡ y mod k = k ∣ distℕ x y

{-
mod-reflexive :
  (k : ℕ) → {!!}
mod-reflexive k {x} = 0ℕ , right-unit-law-mulℕ k ∙ distℕ-refl x
 
mod-sym :
  (k : ℕ) → {!!}
mod-sym k {x} {y} (l , k*l≡distℕxy) = l , k*l≡distℕxy ∙ distℕ-sym x y
-}

-- 7.3 The standard finite types

classical-Fin : ℕ → UU
classical-Fin k = Σ x ∶ ℕ , (x < k)

Fin' : ℕ → UU
Fin' 0ℕ = Φ
Fin' (succℕ k) = Fin' k ∔ 𝟏

★' : {k : ℕ}
  → Fin' (succℕ k)
★' = inr ＊

𝓲' : {k : ℕ}
  → Fin' k → Fin' (succℕ k)
𝓲' = inl

ι' : (k : ℕ)
  → Fin' k → ℕ
ι' (succℕ k) (inl x) = ι' k x
ι' (succℕ k) (inr ＊) = k

data Fin : ℕ → UU where
  ★ : {k : ℕ} → Fin (succℕ k)
  𝓲  : {k : ℕ} → Fin k → Fin (succℕ k)

ind-Fin : {P : {k : ℕ} → Fin k → UU i}
  → (g : (k : ℕ) (x : Fin k) → P {k} x → P {succℕ k} (𝓲 x))
  → (p : (k : ℕ) → P {succℕ k} ★)
  → {k : ℕ} (x : Fin k) → P {k} x
ind-Fin g p {succℕ k} ★    = p k
ind-Fin g p {succℕ k} (𝓲 x) = g k x (ind-Fin g p {k} x)

ι : {k : ℕ} → Fin k → ℕ
ι {succℕ k} ★ = k
ι {succℕ k} (𝓲 x) = ι {k} x

ι-inj : {k : ℕ}
  → (x y : Fin k)
  → ι {k} x ≡ ι {k} y → x ≡ y
ι-inj ★ ★ p = refl ★
ι-inj ★ (𝓲 y) p = ex-falso (g p)
  where
    postulate
      g : {k : ℕ} {y : Fin k}
        → ι {succℕ k} ★ ≢ ι {succℕ k} (𝓲 y)
ι-inj (𝓲 x) ★ p = ex-falso (f p)
  where
    postulate
      f : {k : ℕ} {x : Fin k}
        → ι {succℕ k} (𝓲 x) ≢ ι {succℕ k} ★
ι-inj (𝓲 x) (𝓲 y) p = ap 𝓲 (ι-inj x y p)

-- 7.4 The natrual numbers modulo k+1

is-split-surjective : {A : UU i} {B : UU j}
  → (A → B) → UU (i ⊔ j)
is-split-surjective {A = A} {B = B} f
  = (b : B) → Σ a ∶ A , (f a ≡ b)

zero : {k : ℕ}
  → Fin (succℕ k)
zero {0ℕ} = ★
zero {succℕ k} = 𝓲 (zero {k})

skip-zero : {k : ℕ}
  → Fin k → Fin (succℕ k)
skip-zero {succℕ k} ★ = ★
skip-zero {succℕ k} (𝓲 x) = 𝓲 (skip-zero {k} x)

succ : {k : ℕ}
  → Fin k → Fin k
succ {succℕ k} ★ = zero {k}
succ {succℕ k} (𝓲 x) = skip-zero {k} x
