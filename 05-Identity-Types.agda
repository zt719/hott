module 05-Identity-Types where

open import 04-Inductive-Types public

-- 5.1 The inductive definition of identity types

infix  4 _≡_
data _≡_ {A : UU ℓ₁} : A → A → UU ℓ₁ where
  refl : (a : A) → a ≡ a
{-# BUILTIN EQUALITY _≡_  #-}

infix  4 _≢_
_≢_ : {A : UU ℓ₁}
  → A → A → UU ℓ₁
A ≢ B = ¬ (A ≡ B)

ind-eq : {A : UU ℓ₁} {a : A} {P : (x : A) (p : a ≡ x) → UU ℓ₂}
  → P a (refl a)
  → (x : A) (p : a ≡ x) → P x p
ind-eq p a (refl .a) = p

-- 5.2 The groupoidal structures of types

concat : {A : UU ℓ₁} {x y z : A}
  → x ≡ y → y ≡ z → x ≡ z
concat (refl x) q = q

infixl 7 _∙_
_∙_ = concat

inv : {A : UU ℓ₁} {x y : A}
  → x ≡ y → y ≡ x
inv (refl x) = refl x

assoc : {A : UU ℓ₁} {x y z w : A}
  → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc (refl x) (refl x) (refl x) = refl (refl x)

left-unit : {A : UU ℓ₁} {x y : A}
  → (p : x ≡ y)
  → refl x ∙ p ≡ p
left-unit (refl x) = refl (refl x)

right-unit : {A : UU ℓ₁} {x y : A}
  → (p : x ≡ y)
  → p ∙ refl y ≡ p
right-unit (refl x) = refl (refl x)

left-inv : {A : UU ℓ₁} {x y : A}
  → (p : x ≡ y)
  → inv p ∙ p ≡ refl y
left-inv (refl x) = refl (refl x)

right-inv : {A : UU ℓ₁} {x y : A}
  → (p : x ≡ y)
  → p ∙ inv p ≡ refl x
right-inv (refl x) = refl (refl x)

-- 5.3 The action on identification of functions

ap : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B) {x y : A}
  → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

ap-id : {A : UU ℓ₁} {x y : A}
  → (p : x ≡ y)
  → p ≡ ap id p
ap-id (refl x) = refl (refl x)

ap-comp : {A : UU ℓ₁} {B : UU ℓ₂} {C : UU ℓ₃} {x y : A}
  → (f : A → B)
  → (g : B → C)
  → (p : x ≡ y)
  → ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp f g (refl x) = refl (refl (g (f x)))

ap-refl : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B)
  → (x : A)
  → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-inv : {A : UU ℓ₁} {B : UU ℓ₂} {x y : A}
  → (f : A → B)
  → (p : x ≡ y)
  → ap f (inv p) ≡ inv (ap f p)
ap-inv f (refl x) = refl (ap f (refl x))

ap-concat : {A : UU ℓ₁} {B : UU ℓ₂} {x y z : A}
  → (f : A → B)
  → (p : x ≡ y) (q : y ≡ z)
  → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-concat f (refl x) (refl x) = refl (ap f (refl x))

-- 5.4 Transport

tr : {A : UU ℓ₁} {x y : A}
  → (B : A → UU ℓ₂)
  → x ≡ y → B x → B y
tr B (refl x) = id

apd : {A : UU ℓ₁} {B : A → UU ℓ₂} {x y : A}
  → (f : (a : A) → B a)
  → (p : x ≡ y)
  → tr B p (f x) ≡ f y
apd f (refl x) = refl (f x)

--5.5 The uniqueness of refl

unique-refl : {A : UU ℓ₁}
  → (a : A)
  → (y : Σ[ x ∈ A ] (a ≡ x))
  → (a , refl a) ≡ y
unique-refl a (a , refl a) = refl (a , refl a)

--5.6 The laws of addition on ℕ

left-unit-+ : (n : ℕ)
  → 0 + n ≡ n
left-unit-+ zero = refl zero
left-unit-+ (suc n) = ap suc (left-unit-+ n)

right-unit-+ : (n : ℕ)
  → n + 0 ≡ n
right-unit-+ n = refl n

left-succ-+ : (m n : ℕ)
  → suc m + n ≡ suc (m + n)
left-succ-+ m zero = refl (suc m)
left-succ-+ m (suc n) = ap suc (left-succ-+ m n)

right-succ-+ : (m n : ℕ)
  → m + suc n ≡ suc (m + n)
right-succ-+ m n = refl (suc (m + n))

assoc-+ : (m n k : ℕ)
  → (m + n) + k ≡ m + (n + k)
assoc-+ m n zero = refl (m + n)
assoc-+ m n (suc k) = ap suc (assoc-+ m n k)

com-+ : (m n : ℕ)
  → m + n ≡ n + m
com-+ zero n = left-unit-+ n
com-+ (suc m) n = left-succ-+ m n ∙ ap suc (com-+ m n)

-- Exercises

distributive-inv-concat : {A : UU ℓ₁} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z)
  → inv (p ∙ q) ≡ inv q ∙ inv p
distributive-inv-concat (refl x) (refl x) = refl (refl x)

inv-con : {A : UU ℓ₁} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  → (p ∙ q ≡ r)
  → (q ≡ inv p ∙ r)
inv-con (refl x) (refl x) (refl x) (refl (refl x)) =
  refl (refl x)

lift : {A : UU ℓ₁} {a x : A}
  → (B : A → UU ℓ₂)
  → (p : a ≡ x) (b : B a)
  → (a , b) ≡ (x , tr B p b)
lift B (refl a) b = refl (a , b)

Mac-lane-pentagon : {A : UU ℓ₁} {a b c d e : A}
  → (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e)
  → let α₁ = (ap (λ t → t ∙ s) (assoc p q r))
        α₂ = (assoc p (q ∙ r) s)
        α₃ = (ap (λ t → p ∙ t) (assoc q r s))
        α₄ = (assoc (p ∙ q) r s)
        α₅ = (assoc p q (r ∙ s))
    in ((α₁ ∙ α₂) ∙ α₃) ≡ (α₄ ∙ α₅)
Mac-lane-pentagon (refl x) (refl x) (refl x) (refl x) = refl (refl (refl x))

left-unit-* : (m : ℕ) → 0 * m ≡ 0
left-unit-* m = refl zero

right-unit-* : (m : ℕ) → m * 0 ≡ 0
right-unit-* zero = refl zero
right-unit-* (suc m) = right-unit-* m

left-id-* : (m : ℕ) → 1 * m ≡ m
left-id-* zero = refl zero
left-id-* (suc m) = ap suc (left-id-* m)

right-id-* : (m : ℕ) → m * 1 ≡ m
right-id-* zero = refl zero
right-id-* (suc m) = ap suc (right-id-* m)

left-succ-* : (m n : ℕ) → suc m * n ≡ m * n + n
left-succ-* m n = refl (m * n + n)

right-succ-* : (m n : ℕ) → m * suc n ≡ m + m * n
right-succ-* zero n = refl zero
right-succ-* (suc m) n
  = ap (λ t → suc (t + n)) (right-succ-* m n)
  ∙ ap suc (assoc-+ m (m * n) n)
  ∙ inv (left-succ-+ m ((m * n) + n))

com-* : (m n : ℕ) → m * n ≡ n * m
com-* zero n = inv (right-unit-* n)
com-* (suc m) n
  = (com-+ (m * n) n)
  ∙ ap (n +_) (com-* m n)
  ∙ inv (right-succ-* n m)

*+-left-distr : (m n k : ℕ) → m * (n + k) ≡ m * n + m * k
*+-left-distr m n zero = ap (m * n +_) (inv (right-unit-* m))
*+-left-distr m n (suc k)
  = right-succ-* m (n + k)
  ∙ ap (m +_) (*+-left-distr m n k)
  ∙ inv (assoc-+ m (m * n) (m * k))
  ∙ ap (_+ m * k) (com-+ m (m * n))
  ∙ assoc-+ (m * n) m (m * k)
  ∙ ap (m * n +_) (inv (right-succ-* m k))

*+-right-distr : (m n k : ℕ) → (m + n) * k ≡ m * k + n * k
*+-right-distr m n zero =
  right-unit-* (m + n)
  ∙ inv (ap (m * 0 +_) (right-unit-* n) ∙ right-unit-* m)
*+-right-distr m n (suc k)
  = right-succ-* (m + n) k
  ∙ ap (m + n +_) (*+-right-distr m n k)
  ∙ assoc-+ m n (m * k + n * k)
  ∙ ap (m +_)
    ( inv (assoc-+ n (m * k) (n * k))
    ∙ ap (_+ n * k) (com-+ n (m * k))
    ∙ assoc-+ (m * k) n (n * k)
    )
  ∙ inv
    ( (ap (_+ n * suc k) (right-succ-* m k))
    ∙ (ap (m + m * k +_) (right-succ-* n k))
    ∙ (assoc-+ m (m * k) (n + n * k ))
    )
    
succpredℤ : (n : ℤ) → succℤ (predℤ n) ≡ n
succpredℤ (inl n) = refl (in-neg n)
succpredℤ (inr (inl ＊)) = refl 0ℤ
succpredℤ (inr (inr zero)) = refl 1ℤ
succpredℤ (inr (inr (suc n))) = refl (in-pos (suc n))

predsuccℤ : (n : ℤ) → predℤ (succℤ n) ≡ n
predsuccℤ (inl zero) = refl -1ℤ
predsuccℤ (inl (suc n)) = refl (in-neg (suc n))
predsuccℤ (inr (inl ＊)) = refl 0ℤ
predsuccℤ (inr (inr n)) = refl (in-pos n)
