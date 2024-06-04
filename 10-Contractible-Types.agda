module 10-Contractible-Types where

open import 09-Equivalences public

-- 10.1 Contractible types

is-contr : (A : UU i) → UU i
is-contr A = Σ c ∶ A , ((x : A) → c ≡ x)

center : {A : UU i}
  → is-contr A → A
center (c , C) = c

contraction : {A : UU i}
  → (a : is-contr A)
  → const (center a) ~ id A
contraction (c , C) = C

𝟏-is-contr : is-contr 𝟏
𝟏-is-contr = (＊ , ind𝟏 (refl ＊))


Σ≡-is-contr : {A : UU i}
  → (a : A) → is-contr (Σ x ∶ A , (a ≡ x))
Σ≡-is-contr a = ((a , refl a) , unique-refl a)

is-contr-is-equiv-to-𝟏 : {A : UU i}
  → is-contr A
  → is-equiv (const ＊)
is-contr-is-equiv-to-𝟏 (c , C)
  = (const c , contraction 𝟏-is-contr)
  , (const c , C)

is-equiv-to-𝟏-is-contr : {A : UU i}
  → is-equiv (const {A = A} ＊)
  → is-contr A
is-equiv-to-𝟏-is-contr ((s , is-sec) , (retr , is-retr))
  = (retr ＊ , is-retr)

-- 10.2 Singleton induction

ev-pt : (A : UU i) (B : A → UU j)
  → (a : A)
  → ((x : A) → B x) → B a
ev-pt A B a f = f a

sat-sing-ind : (A : UU i) (B : A → UU j)
  → (a : A) → UU (i ⊔ j)
sat-sing-ind A B a = sec (ev-pt A B a)

ind-sing : (A : UU i) (B : A → UU j)
  → (a : A)
  → sat-sing-ind A B a
  → B a
  → (x : A) → B x
ind-sing A B a (s , is-sec) = s

comp-sing : (A : UU i) (B : A → UU j)
  → (a : A) (ssi : sat-sing-ind A B a)
  → (ev-pt A B a ∘ ind-sing A B a ssi ~ id (B a))
comp-sing A B a (s , is-sec) = is-sec

𝟏-sat-sing-ind : {B : 𝟏 → UU i}
  → sat-sing-ind 𝟏 B ＊
𝟏-sat-sing-ind = ind𝟏 , (λ a → refl a)

is-contr-sat-sing-ind : (A : UU i) (B : A → UU j)
  → is-contr A
  → (a : A) → sat-sing-ind A B a
is-contr-sat-sing-ind A B (_ , C) a
  = (ind-s , comp-s)
  where
  ind-s : B a → (x : A) → B x
  ind-s b x = tr B (inv (C a) ∙ C x) b

  comp-s : ev-pt A B a ∘ ind-s ~ id (B a)
  comp-s b = ap (λ ω → tr B ω b) (left-inv (C a))

postulate
  sat-sing-ind-is-contr : (A : UU i) (B : A → UU i)
    → (a : A) → (sat-sing-ind A B a → is-contr A)
  -- sat-sing-ind-is-contr A B a S = a , λ x → {!!}

-- 10.3 Contractible maps

fib : {A : UU i} {B : UU j}
  → (f : A → B) (b : B) → UU (i ⊔ j)
fib {A = A} f b = Σ a ∶ A , (f a ≡ b)

Eq-fib : {A : UU i} {B : UU j} {y : B}
  → (f : A → B) → (xp xp′ : fib f y) → UU (i ⊔ j)
Eq-fib f (x , p) (x′ , p′) = Σ α ∶ x ≡ x′ , (p ≡ ap f α ∙ p′)

Eq-fib-reflexive : {A : UU i} {B : UU j} {y : B}
  → (f : A → B) (xp : fib f y) → Eq-fib f xp xp
Eq-fib-reflexive f (x , refl .(f x)) = ((refl x) , refl (refl (f x)))

≡→Eq-fib : {A : UU i} {B : UU j} {y : B}
  → (f : A → B) (xp xp′ : fib f y)
  → xp ≡ xp′ → Eq-fib f xp xp′
≡→Eq-fib f xp .xp (refl .xp) = Eq-fib-reflexive f xp

Eq-fib→≡-is-equiv : {A : UU i} {B : UU j} {y : B}
  → (f : A → B) (xp xp′ : fib f y)
  → is-equiv (≡→Eq-fib f xp xp′)
Eq-fib→≡-is-equiv f xp xp′
  = (Eq-fib→≡ f xp xp′ , is-sec f xp xp′)
  , (Eq-fib→≡ f xp xp′ , is-retr f xp xp′)
  where
  Eq-fib→≡ : {A : UU i} {B : UU j} {y : B}
    → (f : A → B) (xp xp′ : fib f y)
    → Eq-fib f xp xp′ → xp ≡ xp′
  Eq-fib→≡ f (x , refl .(f x)) (.x , refl .(f x)) (refl .x , refl .(refl (f x)))
    = refl (x , refl (f x))

  is-sec :  {A : UU i} {B : UU j} {y : B}
    → (f : A → B) (xp xp′ : fib f y)
    → ≡→Eq-fib f xp xp′ ∘ Eq-fib→≡ f xp xp′ ~ id (Eq-fib f xp xp′)
  is-sec f (x , refl .(f x)) (.x , refl .(f x)) (refl .x , refl .(refl (f x)))
    = refl (refl x , refl (refl (f x)))

  is-retr :  {A : UU i} {B : UU j} {y : B}
    → (f : A → B) (xp xp′ : fib f y)
    → Eq-fib→≡ f xp xp′ ∘ ≡→Eq-fib f xp xp′ ~ id (xp ≡ xp′)
  is-retr f (x , refl .(f x)) (.x , refl .(f x)) (refl (.x , refl .(f x)))
    = refl (refl (x , refl (f x)))

{-
-- 10.4 Equivalences are contractible maps

is-contr-map : {A : UU i} {B : UU j}
  → (f : A → B) UU (i ⊔ j)
is-contr-map {B = B} f = (b : B) is-contr (fib f b)

{-
is-contr-map-is-equiv : {A : UU i} {B : UU j}
  → (f : A → B) (is-contr-map f → is-equiv f)
is-contr-map-is-equiv {A = A} {B = B} f is-contr-map-f
  = (g , G)
  , (g , {!!})
  where
  df : (y : B) fib f y
  df y = center (is-contr-map-f y)

  g : B → A
  g y = pr₁ (df y)

  G : (y : B) (f (g y) ≡ y)
  G y = pr₂ (df y)

  p : (x : A) (f (g (f x)) ≡ f x)
  p x = G (f x)

  q : (x : A) ((g (f x) , p x) ≡ (x , refl (f x)))
  q x = {!is-contr-map-f (f x)!}
-}
-}
