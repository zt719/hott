module 06-Universes where

open import 05-Identity-Types public

-- 6.3 Observational equality of the ℕ

Eqℕ : ℕ → ℕ → UU
Eqℕ zero zero = 𝟙
Eqℕ zero (suc m) = 𝟘
Eqℕ (suc n) zero = 𝟘
Eqℕ (suc n) (suc m) = Eqℕ n m

refl-Eqℕ : (n : ℕ) → Eqℕ n n
refl-Eqℕ zero = ＊
refl-Eqℕ (suc n) = refl-Eqℕ n

Eqℕ→≡  : {m n : ℕ} → Eqℕ m n → m ≡ n
Eqℕ→≡ {zero} {zero} = λ x → refl zero
Eqℕ→≡ {zero} {suc n} = ind𝟘
Eqℕ→≡ {suc m} {zero} = ind𝟘
Eqℕ→≡ {suc m} {suc n} = ap suc ∘ Eqℕ→≡ {m} {n}

≡→Eqℕ : {m n : ℕ} → m ≡ n → Eqℕ m n
≡→Eqℕ {.zero} {.zero} (refl zero) = ＊
≡→Eqℕ {.(suc m)} {.(suc m)} (refl (suc m)) = ≡→Eqℕ (refl m)

≡↔Eqℕ : {m n : ℕ} → m ≡ n ↔ Eqℕ m n
≡↔Eqℕ = ≡→Eqℕ , Eqℕ→≡

-- 6.4 Peano's seventh and eighth axioms

inj-suc : {m n : ℕ} → suc m ≡ suc n → m ≡ n
inj-suc = pr₂ ≡↔Eqℕ ∘ pr₁ ≡↔Eqℕ

peanos7 : {m n : ℕ} → m ≡ n ↔ suc m ≡ suc n
peanos7 = ap suc , inj-suc

peanos8 : {n : ℕ} → zero ≢ suc n
peanos8 {n} = pr₁ (≡↔Eqℕ {zero} {suc n})

-- Exercises

inj-+k : {m n k : ℕ} → m + k ≡ n + k → m ≡ n
inj-+k {k = zero} p = p
inj-+k {k = suc k} p = inj-+k (pr₂ peanos7 p)

6-1a1 : {m n k : ℕ} → m ≡ n ↔ m + k ≡ n + k
6-1a1 {k = k} = ap (_+ k) , inj-+k

postulate
  *sk-inj : {m n k : ℕ} → m * suc k ≡ n * suc k → m ≡ n
    
6-1a2 : {m n k : ℕ} → m ≡ n ↔ m * suc k ≡ n * suc k
6-1a2 {k = k} = (ap (_* suc k) , *sk-inj)

Eq-Bool : Bool → Bool → UU
Eq-Bool false false = 𝟙
Eq-Bool false true = 𝟘
Eq-Bool true false = 𝟘
Eq-Bool true true = 𝟙

≡→Eq-Bool : {x y : Bool} → x ≡ y → Eq-Bool x y
≡→Eq-Bool (refl false) = ＊
≡→Eq-Bool (refl true) = ＊

Eq-Bool→≡ : {x y : Bool} → Eq-Bool x y → x ≡ y
Eq-Bool→≡ {false} {false} ＊ = refl false
Eq-Bool→≡ {true} {true} ＊ = refl true

≡↔Eq-Bool : {x y : Bool} → x ≡ y ↔ Eq-Bool x y
≡↔Eq-Bool = ≡→Eq-Bool , Eq-Bool→≡

b≢neg-Bool-b : {b : Bool} → b ≢ neg-Bool b
b≢neg-Bool-b {false} p = ≡→Eq-Bool p
b≢neg-Bool-b {true} p = ≡→Eq-Bool p

f≢t : false ≢ true
f≢t p = ≡→Eq-Bool p

infix  4 _≤_
_≤_ : ℕ → ℕ → UU
zero ≤ zero = 𝟙
zero ≤ suc n = 𝟙
suc m ≤ zero = 𝟘
suc m ≤ suc n = m ≤ n

refl-≤ : {n : ℕ} → n ≤ n
refl-≤ {zero} = ＊
refl-≤ {suc n} = refl-≤ {n}

antisym-≤ : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
antisym-≤ {zero} {zero} ＊ ＊ = refl zero
antisym-≤ {suc m} {suc n} p q = ap suc (antisym-≤ {m} {n} p q)

trans-≤ : {m n h : ℕ} → m ≤ n → n ≤ h → m ≤ h
trans-≤ {zero} {zero} {zero} p q = ＊
trans-≤ {zero} {zero} {suc h} p q = ＊
trans-≤ {zero} {suc n} {suc h} p q = ＊
trans-≤ {suc m} {suc n} {suc h} p q = trans-≤ {m} {n} {h} p q

total-≤ : {m n : ℕ} → m ≤ n ⊎ n ≤ m
total-≤ {zero} {zero} = inl ＊
total-≤ {zero} {suc n} = inl ＊
total-≤ {suc m} {zero} = inr ＊
total-≤ {suc m} {suc n} = total-≤ {m} {n}

infix  4 _<_
_<_ : ℕ → ℕ → UU
zero < zero = 𝟘
zero < suc n = 𝟙
suc m < zero = 𝟘
suc m < suc n = m < n

infix  4 _≮_
_≮_ : ℕ → ℕ → UU₀
m ≮ n = ¬ (m < n)

antirefl-< : (x : ℕ) → x ≮ x
antirefl-< zero = id
antirefl-< (suc x) = antirefl-< x

antisym-< : (x y : ℕ) → x < y → y ≮ x
antisym-< zero (suc y) x<y = id
antisym-< (suc x) (suc y) x<y = antisym-< x y x<y

trans-< : (x y z : ℕ) → x < y → y < z → x < z
trans-< zero (suc y) (suc z) x<y y<z = ＊
trans-< (suc x) (suc y) (suc z) x<y y<z = trans-< x y z x<y y<z

distℕ : ℕ → ℕ → ℕ
distℕ zero zero = zero
distℕ zero (suc y) = suc y
distℕ (suc x) zero = suc x
distℕ (suc x) (suc y) = distℕ x y

distℕ-refl : (x : ℕ) → zero ≡ distℕ x x
distℕ-refl zero = refl zero
distℕ-refl (suc x) = distℕ-refl x

distℕ-sym : (x y : ℕ) → distℕ x y ≡ distℕ y x
distℕ-sym zero zero = refl zero
distℕ-sym zero (suc y) = refl (suc y)
distℕ-sym (suc x) zero = refl (suc x)
distℕ-sym (suc x) (suc y) = distℕ-sym x y

  
  
