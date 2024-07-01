module 05-Identity-Types where

open import 04-Inductive-Types public

-- 5.1 The inductive definition of identity types

data _≡_ {A : UU l₁} : A → A → UU l₁ where
  refl : (a : A) → a ≡ a
infix  4 _≡_

_≢_ : {A : UU l₁}
  → A → A → UU l₁
A ≢ B = ¬ (A ≡ B)
infix  4 _≢_

ind≡ : {A : UU l₁} {a : A} {P : (x : A) (p : a ≡ x) → UU l₂}
  → P a (refl a)
  → (x : A) (p : a ≡ x) → P x p
ind≡ p a (refl a) = p

-- 5.2 The groupoidal structures of types

concat : {A : UU l₁} {x y z : A}
  → x ≡ y → y ≡ z → x ≡ z
concat (refl x) q = q

_∙_ = concat
infixl 7 _∙_

inv : {A : UU l₁} {x y : A}
  → x ≡ y → y ≡ x
inv (refl x) = refl x

assoc : {A : UU l₁} {x y z w : A}
  → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc (refl x) (refl x) (refl x) = refl (refl x)

left-unit : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → refl x ∙ p ≡ p
left-unit (refl x) = refl (refl x)

right-unit : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → p ∙ refl y ≡ p
right-unit (refl x) = refl (refl x)

left-inv : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → inv p ∙ p ≡ refl y
left-inv (refl x) = refl (refl x)

right-inv : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → p ∙ inv p ≡ refl x
right-inv (refl x) = refl (refl x)

-- 5.3 The action on identification of functions

ap : {A : UU l₁} {B : UU l₂}
  → (f : A → B) {x y : A}
  → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

ap-id : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → p ≡ ap id p
ap-id (refl x) = refl (refl x)

ap-comp : {A : UU l₁} {B : UU l₂} {C : UU l₃} {x y : A}
  → (f : A → B)
  → (g : B → C)
  → (p : x ≡ y)
  → ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp f g (refl x) = refl (refl (g (f x)))

ap-refl : {A : UU l₁} {B : UU l₂}
  → (f : A → B)
  → (x : A)
  → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-inv : {A : UU l₁} {B : UU l₂} {x y : A}
  → (f : A → B)
  → (p : x ≡ y)
  → ap f (inv p) ≡ inv (ap f p)
ap-inv f (refl x) = refl (ap f (refl x))

ap-concat : {A : UU l₁} {B : UU l₂} {x y z : A}
  → (f : A → B)
  → (p : x ≡ y) (q : y ≡ z)
  → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-concat f (refl x) (refl x) = refl (ap f (refl x))

-- 5.4 Transport

tr : {A : UU l₁} {x y : A}
  → (B : A → UU l₂)
  → x ≡ y → B x → B y
tr B (refl x) = id

apd : {A : UU l₁} {B : A → UU l₂} {x y : A}
  → (f : (a : A) → B a)
  → (p : x ≡ y)
  → tr B p (f x) ≡ f y
apd f (refl x) = refl (f x)

--5.5 The uniqueness of refl

unique-refl : {A : UU l₁}
  → (a : A)
  → (y : Σ x ∶ A , (a ≡ x))
  → (a , refl a) ≡ y
unique-refl a (a , refl a) = refl (a , refl a)

--5.6 The laws of addition on ℕ

left-unit-+ : (n : ℕ)
  → 0 + n ≡ n
left-unit-+ 0ℕ = refl 0ℕ
left-unit-+ (succℕ n) = ap succℕ (left-unit-+ n)

right-unit-+ : (n : ℕ)
  → n + 0 ≡ n
right-unit-+ n = refl n

left-succ-+ : (m n : ℕ)
  → succℕ m + n ≡ succℕ (m + n)
left-succ-+ m 0ℕ = refl (succℕ m)
left-succ-+ m (succℕ n) = ap succℕ (left-succ-+ m n)

right-succ-+ : (m n : ℕ)
  → m + succℕ n ≡ succℕ (m + n)
right-succ-+ m n = refl (succℕ (m + n))

assoc-+ : (m n k : ℕ)
  → (m + n) + k ≡ m + (n + k)
assoc-+ m n 0ℕ = refl (m + n)
assoc-+ m n (succℕ k) = ap succℕ (assoc-+ m n k)

com-+ : (m n : ℕ)
  → m + n ≡ n + m
com-+ 0ℕ n = left-unit-+ n
com-+ (succℕ m) n = left-succ-+ m n ∙ ap succℕ (com-+ m n)

-- Exercises

distributive-inv-concat : {A : UU l₁} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z)
  → inv (p ∙ q) ≡ inv q ∙ inv p
distributive-inv-concat (refl x) (refl x) = refl (refl x)

inv-con : {A : UU l₁} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  → (p ∙ q ≡ r)
  → (q ≡ inv p ∙ r)
inv-con (refl x) (refl x) (refl x) (refl (refl x)) =
  refl (refl x)

lift : {A : UU l₁} {a x : A}
  → (B : A → UU l₂)
  → (p : a ≡ x) (b : B a)
  → (a , b) ≡ (x , tr B p b)
lift B (refl a) b = refl (a , b)

Mac-lane-pentagon : {A : UU l₁} {a b c d e : A}
  → (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e)
  → let α₁ = (ap (λ t → t ∙ s) (assoc p q r))
        α₂ = (assoc p (q ∙ r) s)
        α₃ = (ap (λ t → p ∙ t) (assoc q r s))
        α₄ = (assoc (p ∙ q) r s)
        α₅ = (assoc p q (r ∙ s))
    in ((α₁ ∙ α₂) ∙ α₃) ≡ (α₄ ∙ α₅)
Mac-lane-pentagon (refl x) (refl x) (refl x) (refl x) = refl (refl (refl x))

left-unit-* : (m : ℕ)
  → 0 * m ≡ 0
left-unit-* m = refl 0ℕ

right-unit-* : (m : ℕ)
  → m * 0 ≡ 0
right-unit-* 0ℕ = refl 0ℕ
right-unit-* (succℕ m) = right-unit-* m

left-id-* : (m : ℕ)
  → 1 * m ≡ m
left-id-* 0ℕ = refl 0ℕ
left-id-* (succℕ m) = ap succℕ (left-id-* m)

right-id-* : (m : ℕ)
  → m * 1 ≡ m
right-id-* 0ℕ = refl 0ℕ
right-id-* (succℕ m) = ap succℕ (right-id-* m)

left-succ-* : (m n : ℕ)
  → succℕ m * n ≡ m * n + n
left-succ-* m n = refl (m * n + n)

right-succ-* : (m n : ℕ)
  → m * succℕ n ≡ m + m * n
right-succ-* 0ℕ n = refl 0ℕ
right-succ-* (succℕ m) n
  = ap (λ t → succℕ (t + n)) (right-succ-* m n)
  ∙ ap succℕ (assoc-+ m (m * n) n)
  ∙ inv (left-succ-+ m ((m * n) + n))

com-* : (m n : ℕ)
  → m * n ≡ n * m
com-* 0ℕ n = inv (right-unit-* n)
com-* (succℕ m) n
  = (com-+ (m * n) n)
  ∙ ap (n +_) (com-* m n)
  ∙ inv (right-succ-* n m)

*+-left-distr : (m n k : ℕ)
  → m * (n + k) ≡ m * n + m * k
*+-left-distr m n 0ℕ = ap (m * n +_) (inv (right-unit-* m))
*+-left-distr m n (succℕ k)
  = right-succ-* m (n + k)
  ∙ ap (m +_) (*+-left-distr m n k)
  ∙ inv (assoc-+ m (m * n) (m * k))
  ∙ ap (_+ m * k) (com-+ m (m * n))
  ∙ assoc-+ (m * n) m (m * k)
  ∙ ap (m * n +_) (inv (right-succ-* m k))

*+-right-distr : (m n k : ℕ)
  → (m + n) * k ≡ m * k + n * k
*+-right-distr m n 0ℕ =
  right-unit-* (m + n)
  ∙ inv (ap (m * 0 +_) (right-unit-* n) ∙ right-unit-* m)
*+-right-distr m n (succℕ k)
  = right-succ-* (m + n) k
  ∙ ap (m + n +_) (*+-right-distr m n k)
  ∙ assoc-+ m n (m * k + n * k)
  ∙ ap (m +_)
    ( inv (assoc-+ n (m * k) (n * k))
    ∙ ap (_+ n * k) (com-+ n (m * k))
    ∙ assoc-+ (m * k) n (n * k)
    )
  ∙ inv
    ( (ap (_+ n * succℕ k) (right-succ-* m k))
    ∙ (ap (m + m * k +_) (right-succ-* n k))
    ∙ (assoc-+ m (m * k) (n + n * k ))
    )
    
succpredℤ : (n : ℤ)
  → succℤ (predℤ n) ≡ n
succpredℤ (inl n) = refl (in-neg n)
succpredℤ (inr (inl ＊)) = refl 0ℤ
succpredℤ (inr (inr 0ℕ)) = refl 1ℤ
succpredℤ (inr (inr (succℕ n))) = refl (in-pos (succℕ n))

predsuccℤ : (n : ℤ)
  → predℤ (succℤ n) ≡ n
predsuccℤ (inl 0ℕ) = refl -1ℤ
predsuccℤ (inl (succℕ n)) = refl (in-neg (succℕ n))
predsuccℤ (inr (inl ＊)) = refl 0ℤ
predsuccℤ (inr (inr n)) = refl (in-pos n)
