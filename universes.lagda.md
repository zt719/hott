```agda

module Universes where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import Agda.Builtin.Equality
  renaming (_≡_ to _≐_; refl to equal)

open import Pi
open import Sigma
open import Naturals
open import Empty
open import Unit
open import Coproducts
open import Identity

-- Observational Equality

Eqℕ : ℕ ⇒ ℕ ⇒ 𝓤₀
Eqℕ 0ℕ 0ℕ = 𝟙
Eqℕ 0ℕ (succℕ m) = Φ
Eqℕ (succℕ n) 0ℕ = Φ
Eqℕ (succℕ n) (succℕ m) = Eqℕ n m

refl-Eqℕ :
  Π[ n ∶ ℕ ] Eqℕ n n
refl-Eqℕ 0ℕ = ＊
refl-Eqℕ (succℕ n) = refl-Eqℕ n

≡⇔Eqℕ :
  Π'[ m n ∶ ℕ ] (m ≡ n ⇔ Eqℕ m n)
≡⇔Eqℕ = (λ{ (refl m) → refl-Eqℕ m }) , f
  where
  f : Π'[ m n ∶ ℕ ] (Eqℕ m n ⇒ m ≡ n)
  f {0ℕ} {0ℕ} = λ x → refl 0ℕ
  f {0ℕ} {succℕ n} = indΦ
  f {succℕ m} {0ℕ} = indΦ
  f {succℕ m} {succℕ n} = ap succℕ ∘ f {m} {n}

-- Peano's seventh and eighth axioms

peanos7 : Π'[ m n ∶ ℕ ]
  (m ≡ n ⇔ succℕ m ≡ succℕ n)
peanos7 = ap succℕ , pr₂ ≡⇔Eqℕ ∘ pr₁ ≡⇔Eqℕ

peanos8 : Π'[ n ∶ ℕ ]
  (0ℕ ≢ succℕ n)
peanos8 {n} = pr₁ (≡⇔Eqℕ {0ℕ} {succℕ n})

{-
6-1a1 : Π[ m , n , k ∶ ℕ ]
  (m ≡ n ⇔ m + k ≡ n + k)
6-1a1 m n 0ℕ = id , id
6-1a1 m n (succℕ k) = (ap (_+ succℕ k)) , {!!}

6-1a2 : Π[ m , n , k ∶ ℕ ]
  (m ≡ n ⇔ m * succℕ k ≡ n * succℕ k)
6-1a2 m n k = ap (_* (k + 1)) , pr₂ ≡⇔Eqℕ ∘ f m n k ∘ pr₁ ≡⇔Eqℕ
  where
  f : Π[ m , n , k ∶ ℕ ]
    (Eqℕ (m * succℕ k) (n * succℕ k) ⇒ Eqℕ m n)
  f m n 0ℕ = {!!}
  f m n (succℕ k) = {!!}

6-1b1 : Π[ m , n ∶ ℕ ]
  (m + n ≡ 0ℕ ⇔ (m ≡ 0 × n ≡ 0))
6-1b1 m n = {!!}

6-1b2 : Π[ m , n ∶ ℕ ]
  (m * n ≡ 0ℕ ⇔ (m ≡ 0ℕ ∔ n ≡ 0ℕ))
6-1b2 m n = {!!}

6-1b3 : Π[ m , n ∶ ℕ ]
  (m * n ≡ 1 ⇔ (m ≡ 1 × n ≡ 1))
6-1b3 m n = {!!}

6-1c1 : Π[ m , n ∶ ℕ ] (m ≢ m + (n + 1))
6-1c1 m n = {!!}
-}

_<_ : ℕ ⇒ ℕ ⇒ 𝓤₀
0ℕ < 0ℕ = Φ
0ℕ < succℕ n = 𝟙
succℕ m < 0ℕ = Φ
succℕ m < succℕ n = m < n
infix  4 _<_

_≮_ : ℕ ⇒ ℕ ⇒ 𝓤₀
m ≮ n = ¬ (m < n)
infix  4 _≮_

_>_ : ℕ ⇒ ℕ ⇒ 𝓤₀
0ℕ > 0ℕ = Φ
0ℕ > succℕ n = Φ
succℕ m > 0ℕ = 𝟙
succℕ m > succℕ n = m > n
infix  4 _>_

<-antirefl : Π[ x ∶ ℕ ] (x ≮ x)
<-antirefl 0ℕ = id Φ
<-antirefl (succℕ x) = <-antirefl x

<-antisym : Π[ x y ∶ ℕ ] (x < y ⇒ y ≮ x)
<-antisym 0ℕ (succℕ y) x<y = id Φ
<-antisym (succℕ x) (succℕ y) x<y = <-antisym x y x<y

ine : Π[ k ∶ ℕ ] (k < succℕ k)
ine 0ℕ = ＊
ine (succℕ k) = ine k

<-trans : Π[ x y z ∶ ℕ ] (x < y ⇒ y < z ⇒ x < z)
<-trans 0ℕ (succℕ y) (succℕ z) x<y y<z = ＊
<-trans (succℕ x) (succℕ y) (succℕ z) x<y y<z = <-trans x y z x<y y<z



```
