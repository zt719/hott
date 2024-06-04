module 06-Universes where

open import 05-Identity-Types public

-- 6.3 Observational equality of the ℕ

Eqℕ : ℕ → ℕ → UU
Eqℕ 0ℕ 0ℕ = 𝟏
Eqℕ 0ℕ (succℕ m) = Φ
Eqℕ (succℕ n) 0ℕ = Φ
Eqℕ (succℕ n) (succℕ m) = Eqℕ n m

refl-Eqℕ : (n : ℕ)
  → Eqℕ n n
refl-Eqℕ 0ℕ = ＊
refl-Eqℕ (succℕ n) = refl-Eqℕ n

Eqℕ→≡  : {m n : ℕ}
  → Eqℕ m n → m ≡ n
Eqℕ→≡ {0ℕ} {0ℕ} = λ x → refl 0ℕ
Eqℕ→≡ {0ℕ} {succℕ n} = indΦ
Eqℕ→≡ {succℕ m} {0ℕ} = indΦ
Eqℕ→≡ {succℕ m} {succℕ n} = ap succℕ ∘ Eqℕ→≡ {m} {n}

≡→Eqℕ : {m n : ℕ}
  → m ≡ n → Eqℕ m n
≡→Eqℕ {.0ℕ} {.0ℕ} (refl 0ℕ) = ＊
≡→Eqℕ {.(succℕ m)} {.(succℕ m)} (refl (succℕ m)) = ≡→Eqℕ (refl m)

≡↔Eqℕ : {m n : ℕ}
  → m ≡ n ↔ Eqℕ m n
≡↔Eqℕ = (≡→Eqℕ , Eqℕ→≡)

-- 6.4 Peano's seventh and eighth axioms

inj-succℕ : {m n : ℕ}
  → succℕ m ≡ succℕ n → m ≡ n
inj-succℕ = pr₂ ≡↔Eqℕ ∘ pr₁ ≡↔Eqℕ

peanos7 : {m n : ℕ}
  → m ≡ n ↔ succℕ m ≡ succℕ n
peanos7 = (ap succℕ , inj-succℕ)

peanos8 : {n : ℕ}
  → 0ℕ ≢ succℕ n
peanos8 {n} = pr₁ (≡↔Eqℕ {0ℕ} {succℕ n})

-- Exercises


6-1a1 : {m n k : ℕ}
  → (m ≡ n ↔ m + k ≡ n + k)
6-1a1 = (to , from)
  where
    to : {m n k : ℕ}
      → (m ≡ n → m + k ≡ n + k)
    to (refl _) = refl _
    
    from : {m n k : ℕ}
      → (m + k ≡ n + k → m ≡ n)
    from {k = 0ℕ} p = p
    from {k = succℕ k} p = from (pr₂ peanos7 p)

{-
6-1a2 : {m n k : ℕ}
  → (m ≡ n ↔ m * succℕ k ≡ n * succℕ k)
6-1a2 {m} {n} {k} = (to , from)
  where
    to : {m n k : ℕ}
      → m ≡ n → m * succℕ k ≡ n * succℕ k
    to (refl _) = refl _
    
    from : {m n k : ℕ}
      → m * succℕ k ≡ n * succℕ k → m ≡ n
    from {m} {n} {k = 0ℕ} p = {!!}
    from {k = succℕ k} p = {!!}
-}

infix  4 _≤_
_≤_ : ℕ → ℕ → UU
0ℕ ≤ 0ℕ = 𝟏
0ℕ ≤ succℕ n = 𝟏
succℕ m ≤ 0ℕ = Φ
succℕ m ≤ succℕ n = m ≤ n

≤-refl : (n : ℕ)
  → n ≤ n
≤-refl 0ℕ = ＊
≤-refl (succℕ n) = ≤-refl n

≤-antisym : (m n : ℕ)
  → m ≤ n → n ≤ m → m ≡ n
≤-antisym 0ℕ 0ℕ ＊ ＊ = refl 0ℕ
≤-antisym (succℕ m) (succℕ n) p q
  = ap succℕ (≤-antisym m n p q)

≤-trans : (m n h : ℕ)
  → m ≤ n → n ≤ h → m ≤ h
≤-trans 0ℕ 0ℕ 0ℕ p q = ＊
≤-trans 0ℕ 0ℕ (succℕ h) p q = ＊
≤-trans 0ℕ (succℕ n) (succℕ h) p q = ＊
≤-trans (succℕ m) (succℕ n) (succℕ h) p q = ≤-trans m n h p q

≤-total : (m n : ℕ)
  → m ≤ n ∔ n ≤ m
≤-total 0ℕ 0ℕ = inl ＊
≤-total 0ℕ (succℕ n) = inl ＊
≤-total (succℕ m) 0ℕ = inr ＊
≤-total (succℕ m) (succℕ n) = ≤-total m n

infix  4 _<_
_<_ : ℕ → ℕ → UU
0ℕ < 0ℕ = Φ
0ℕ < succℕ n = 𝟏
succℕ m < 0ℕ = Φ
succℕ m < succℕ n = m < n

infix  4 _≮_
_≮_ : ℕ → ℕ → UU₀
m ≮ n = ¬ (m < n)


_>_ : ℕ → ℕ → UU₀
0ℕ > 0ℕ = Φ
0ℕ > succℕ n = Φ
succℕ m > 0ℕ = 𝟏
succℕ m > succℕ n = m > n
infix  4 _>_

<-antirefl : (x : ℕ) → x ≮ x
<-antirefl 0ℕ = id Φ
<-antirefl (succℕ x) = <-antirefl x

<-antisym : (x y : ℕ) → x < y → y ≮ x
<-antisym 0ℕ (succℕ y) x<y = id Φ
<-antisym (succℕ x) (succℕ y) x<y = <-antisym x y x<y

ine : (k : ℕ) → k < succℕ k
ine 0ℕ = ＊
ine (succℕ k) = ine k

<-trans : (x y z : ℕ) → x < y → y < z → x < z
<-trans 0ℕ (succℕ y) (succℕ z) x<y y<z = ＊
<-trans (succℕ x) (succℕ y) (succℕ z) x<y y<z = <-trans x y z x<y y<z

