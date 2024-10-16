module 07-Curry-Howard where

open import 06-Universes public

-- 7.1 The Curry-Howard interpretation

_∣_ : (d n : ℕ) → UU₀
d ∣ n = Σ[ k ∈ ℕ ] (d * k ≡ n)

three-divides-six : 3 ∣ 6
three-divides-six = 2 , refl 6

one-dividesℕ : (x : ℕ) → 1 ∣ x
one-dividesℕ x = x , left-id-* x

-- Proposition 7.1.5

p7-1-5 : (x y d : ℕ)
  → d ∣ x × d ∣ y
  → d ∣ (x + y)
p7-1-5 x y d ((k , d*k≡x) , (l , d*l≡y)) = k + l , α ∙ β ∙ γ
  where
  α : d * (k + l) ≡ d * k + d * l
  α = *+-left-distr d k l
  β : d * k + d * l ≡ x + d * l
  β = ap (_+ d * l) d*k≡x
  γ : x + d * l ≡ x + y
  γ = ap (x +_) d*l≡y

-- 7.2 The congruence relations on ℕ

is-refl-R : {A : UU ℓ₁}
  → (R : A → A → UU ℓ₂) → UU (ℓ₁ ⊔ ℓ₂)
is-refl-R R = (x : _) → R x x

is-sym-R : {A : UU ℓ₁}
  → (R : A → A → UU ℓ₂) → UU (ℓ₁ ⊔ ℓ₂)
is-sym-R R = (x y : _) → R x y → R y x

is-trans-R : {A : UU ℓ₁}
  → (R : A → A → UU ℓ₂) → UU (ℓ₁ ⊔ ℓ₂)
is-trans-R R = (x y z : _) → R x y → R y z → R x z

is-equiv-R : {A : UU ℓ₁}
  → (R : A → A → UU ℓ₂) → UU (ℓ₁ ⊔ ℓ₂)
is-equiv-R R = is-refl-R R × is-sym-R R × is-trans-R R

_≡_mod_ : ℕ → ℕ → ℕ → UU
x ≡ y mod k = k ∣ distℕ x y

mod-refl : (k : ℕ)
  → is-refl-R (_≡_mod k)
mod-refl k x = zero , right-unit-* k ∙ distℕ-refl x

mod-sym : (k : ℕ)
  → is-sym-R (_≡_mod k)
mod-sym k x y (l , k*l≡distℕxy) = l , k*l≡distℕxy ∙ distℕ-sym x y

postulate
  mod-trans : (k : ℕ) → is-trans-R (_≡_mod k)

mod-equiv : (k : ℕ) → is-equiv-R (_≡_mod k)
mod-equiv k = mod-refl k , mod-sym k , mod-trans k

-- 7.3 The standard finite types

classical-Fin : ℕ → UU
classical-Fin k = Σ[ x ∈ ℕ ] (x < k)

Fin' : ℕ → UU
Fin' zero = 𝟘
Fin' (suc k) = Fin' k ⊎ 𝟙

zero' : {k : ℕ}
  → Fin' (suc k)
zero' = inr ＊

suc' : {k : ℕ}
  → Fin' k → Fin' (suc k)
suc' = inl

ι' : (k : ℕ)
  → Fin' k → ℕ
ι' (suc k) (inl x) = ι' k x
ι' (suc k) (inr ＊) = k

data Fin : ℕ → UU where
  zero : {k : ℕ} → Fin (suc k)
  suc  : {k : ℕ} → Fin k → Fin (suc k)

ind-Fin : {P : {k : ℕ} → Fin k → UU ℓ₁}
  → (g : (k : ℕ) (x : Fin k) → P {k} x → P {suc k} (suc x))
  → (p : (k : ℕ) → P {suc k} zero)
  → {k : ℕ} (x : Fin k) → P {k} x
ind-Fin g p {suc k} zero    = p k
ind-Fin g p {suc k} (suc x) = g k x (ind-Fin g p {k} x)

ι : {k : ℕ} → Fin k → ℕ
ι {suc k} zero = k
ι {suc k} (suc x) = ι {k} x

ι-inj : {k : ℕ}
  → (x y : Fin k)
  → ι {k} x ≡ ι {k} y → x ≡ y
ι-inj zero zero p = refl zero
ι-inj zero (suc y) p = ex-falso (g p)
  where
    postulate
      g : {k : ℕ} {y : Fin k}
        → ι {suc k} zero ≢ ι {suc k} (suc y)
ι-inj (suc x) zero p = ex-falso (f p)
  where
    postulate
      f : {k : ℕ} {x : Fin k}
        → ι {suc k} (suc x) ≢ ι {suc k} zero
ι-inj (suc x) (suc y) p = ap suc (ι-inj x y p)

-- 7.4 The natrual numbers modulo k+1

is-split-surjective : {A : UU ℓ₁} {B : UU ℓ₂}
  → (A → B) → UU (ℓ₁ ⊔ ℓ₂)
is-split-surjective f
  = (b : _) → Σ[ a ∈ _ ] (f a ≡ b)
