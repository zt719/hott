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
concat (refl x) (refl x) = refl x

_∙_ = concat
infixl 7 _∙_

inv : {A : UU l₁} {x y : A}
  → x ≡ y → y ≡ x
inv (refl x) = refl x

assoc : {A : UU l₁} {x y z w : A}
  → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc (refl x) (refl x) (refl x) = refl (refl x)

unitˡ : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → refl x ∙ p ≡ p
unitˡ (refl x) = refl (refl x)

unitʳ : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → p ∙ refl y ≡ p
unitʳ (refl x) = refl (refl x)

invˡ : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → inv p ∙ p ≡ refl y
invˡ (refl x) = refl (refl x)

invʳ : {A : UU l₁} {x y : A}
  → (p : x ≡ y)
  → p ∙ inv p ≡ refl x
invʳ (refl x) = refl (refl x)

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

unitˡ-+ : (n : ℕ)
  → 0 + n ≡ n
unitˡ-+ 0ℕ = refl 0ℕ
unitˡ-+ (succℕ n) = ap succℕ (unitˡ-+ n)

unitʳ-+ : (n : ℕ)
  → n + 0 ≡ n
unitʳ-+ n = refl n

succˡ-+ : (m n : ℕ)
  → succℕ m + n ≡ succℕ (m + n)
succˡ-+ m 0ℕ = refl (succℕ m)
succˡ-+ m (succℕ n) = ap succℕ (succˡ-+ m n)

succʳ-+ : (m n : ℕ)
  → m + succℕ n ≡ succℕ (m + n)
succʳ-+ m n = refl (succℕ (m + n))

assoc-+ : (m n k : ℕ)
  → (m + n) + k ≡ m + (n + k)
assoc-+ m n 0ℕ = refl (m + n)
assoc-+ m n (succℕ k) = ap succℕ (assoc-+ m n k)

com-+ : (m n : ℕ)
  → m + n ≡ n + m
com-+ 0ℕ n = unitˡ-+ n
com-+ (succℕ m) n = succˡ-+ m n ∙ ap succℕ (com-+ m n)

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

Mac-Lane-pentagon : {A : UU l₁} {a b c d e : A}
  → (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (s : d ≡ e)
  → let α₁ = (ap (λ t → t ∙ s) (assoc p q r))
        α₂ = (assoc p (q ∙ r) s)
        α₃ = (ap (λ t → p ∙ t) (assoc q r s))
        α₄ = (assoc (p ∙ q) r s)
        α₅ = (assoc p q (r ∙ s))
    in ((α₁ ∙ α₂) ∙ α₃) ≡ (α₄ ∙ α₅)
Mac-Lane-pentagon (refl x) (refl x) (refl x) (refl x) = refl (refl (refl x))

unitˡ-* : (m : ℕ)
  → 0 * m ≡ 0
unitˡ-* m = refl 0ℕ

unitʳ-* : (m : ℕ)
  → m * 0 ≡ 0
unitʳ-* 0ℕ = refl 0ℕ
unitʳ-* (succℕ m) = unitʳ-* m

idˡ-* : (m : ℕ)
  → 1 * m ≡ m
idˡ-* 0ℕ = refl 0ℕ
idˡ-* (succℕ m) = ap succℕ (idˡ-* m)

idʳ-* : (m : ℕ)
  → m * 1 ≡ m
idʳ-* 0ℕ = refl 0ℕ
idʳ-* (succℕ m) = ap succℕ (idʳ-* m)

succˡ-* : (m n : ℕ)
  → succℕ m * n ≡ m * n + n
succˡ-* m n = refl (m * n + n)

succʳ-* : (m n : ℕ)
  → m * succℕ n ≡ m + m * n
succʳ-* 0ℕ n = refl 0ℕ
succʳ-* (succℕ m) n
  = ap (λ t → succℕ (t + n)) (succʳ-* m n)
  ∙ ap succℕ (assoc-+ m (m * n) n)
  ∙ inv (succˡ-+ m ((m * n) + n))

com-* : (m n : ℕ)
  → m * n ≡ n * m
com-* 0ℕ n = inv (unitʳ-* n)
com-* (succℕ m) n
  = (com-+ (m * n) n)
  ∙ ap (n +_) (com-* m n)
  ∙ inv (succʳ-* n m)

*+-distrˡ : (m n k : ℕ)
  → m * (n + k) ≡ m * n + m * k
*+-distrˡ m n 0ℕ = ap (m * n +_) (inv (unitʳ-* m))
*+-distrˡ m n (succℕ k)
  = succʳ-* m (n + k)
  ∙ ap (m +_) (*+-distrˡ m n k)
  ∙ inv (assoc-+ m (m * n) (m * k))
  ∙ ap (_+ m * k) (com-+ m (m * n))
  ∙ assoc-+ (m * n) m (m * k)
  ∙ ap (m * n +_) (inv (succʳ-* m k))

*+-distrʳ : (m n k : ℕ)
  → (m + n) * k ≡ m * k + n * k
*+-distrʳ m n 0ℕ =
  unitʳ-* (m + n)
  ∙ inv (ap (m * 0 +_) (unitʳ-* n) ∙ unitʳ-* m)
*+-distrʳ m n (succℕ k)
  = succʳ-* (m + n) k
  ∙ ap (m + n +_) (*+-distrʳ m n k)
  ∙ assoc-+ m n (m * k + n * k)
  ∙ ap (m +_)
    ( inv (assoc-+ n (m * k) (n * k))
    ∙ ap (_+ n * k) (com-+ n (m * k))
    ∙ assoc-+ (m * k) n (n * k)
    )
  ∙ inv
    ( (ap (_+ n * succℕ k) (succʳ-* m k))
    ∙ (ap (m + m * k +_) (succʳ-* n k))
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
