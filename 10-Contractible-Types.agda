module 10-Contractible-Types where

open import 09-Equivalences public

-- 10.1 Contractible types

is-contr : (A : UU l₁) → UU l₁
is-contr A = Σ c ∶ A , ((x : A) → c ≡ x)

center : {A : UU l₁}
  → is-contr A → A
center (c , C) = c

contraction : {A : UU l₁}
  → (a : is-contr A)
  → const (center a) ~ id
contraction (c , C) = C

𝟏-is-contr : is-contr 𝟏
𝟏-is-contr = ＊ , ind𝟏 (refl ＊)

Σa≡x-is-contr : {A : UU l₁}
  → (a : A)
  → is-contr (Σ x ∶ A , (a ≡ x))
Σa≡x-is-contr a = (a , refl a) , unique-refl a

is-contr-is-equiv-to-𝟏 : {A : UU l₁}
  → is-contr A
  → is-equiv (const ＊)
is-contr-is-equiv-to-𝟏 (c , C)
  = (const c , contraction 𝟏-is-contr)
  , (const c , C)

is-equiv-to-𝟏-is-contr : {A : UU l₁}
  → is-equiv (const ＊)
  → is-contr A
is-equiv-to-𝟏-is-contr ((s , is-sec) , (retr , is-retr))
  = retr ＊ , is-retr

-- 10.2 Singleton induction

ev-pt : {A : UU l₁}
  → (a : A)
  → (B : A → UU l₂)
  → ((x : A) → B x) → B a
ev-pt a B f = f a

sing-ind : (l : Level) (A : UU l₁) → A → UU (l₁ ⊔ lsuc l)
sing-ind l A a = (B : A → UU l) → sec (ev-pt a B)

𝟏-sing-ind : sing-ind l₁ 𝟏 ＊
𝟏-sing-ind B = ind𝟏 , λ a → refl a

is-contr→sing-ind : {A : UU l₁}
  → is-contr A
  → (a : A)
  → {l : Level}→ sing-ind l A a
is-contr→sing-ind (c , C) a B
  = ind-s , comp-s
  where
  ind-s : B a → (x : _) → B x
  ind-s b x = tr B (inv (C a) ∙ C x) b

  comp-s : ev-pt a B ∘ ind-s ~ id
  comp-s b = ap (λ ω → tr B ω b) (invˡ (C a))

sing-ind→is-contr : {A : UU l₁}
  → (a : A)
  → ({l : Level} → sing-ind l A a)
  → is-contr A
sing-ind→is-contr a S = ind-sing→is-contr a (λ B → pr₁ (S B))
  where
  ind-sing→is-contr : {A : UU l₁}
    → (a : A)
    → ({l : Level} (B : A → UU l) → B a → (x : A) → B x)
    → is-contr A
  ind-sing→is-contr a S = a , S (a ≡_) (refl a)

-- 10.3 Contractible maps

fib : {A : UU l₁} {B : UU l₂}
  → (f : A → B) (b : B)
  → UU (l₁ ⊔ l₂)
fib f b = Σ a ∶ _ , (f a ≡ b)

Eq-fib : {A : UU l₁} {B : UU l₂}
  → (f : A → B) (y : B) (xp xp' : fib f y)
  → UU (l₁ ⊔ l₂)
Eq-fib f y (x , p) (x' , p') = Σ α ∶ x ≡ x' , (p ≡ ap f α ∙ p')

Eq-fib-refl : {A : UU l₁} {B : UU l₂} 
  → (f : A → B) (y : B)
  → reflexive (Eq-fib f y)
Eq-fib-refl f y (x , refl .(f x)) = (refl x , refl (refl (f x)))

≡→Eq-fib : {A : UU l₁} {B : UU l₂}
  → (f : A → B) (y : B) (xp xp' : fib f y)
  → xp ≡ xp'
  → Eq-fib f y xp xp'
≡→Eq-fib f y xp .xp (refl .xp) = Eq-fib-refl f y xp

Eq-fib→≡ : {A : UU l₁} {B : UU l₂}
  → (f : A → B) (y : B) (xp xp' : fib f y)
  → Eq-fib f y xp xp' → xp ≡ xp'
Eq-fib→≡ f y (x , refl .(f x)) (.x , refl .(f x)) (refl .x , refl .(refl (f x)))
  = refl (x , refl (f x))
  
Eq-fib≃≡ : {A : UU l₁} {B : UU l₂}
  → (f : A → B) (y : B) (xp xp' : fib f y)
  → xp ≡ xp' ≃ Eq-fib f y xp xp'
Eq-fib≃≡ f y xp xp'
  = ≡→Eq-fib f y xp xp'
  , (Eq-fib→≡ f y xp xp' , is-sec f y xp xp')
  , (Eq-fib→≡ f y xp xp' , is-retr f y xp xp')
  where
  is-sec :  {A : UU l₁} {B : UU l₂}
    → (f : A → B) (y : B) (xp xp' : fib f y)
    → ≡→Eq-fib f y xp xp' ∘ Eq-fib→≡ f y xp xp' ~ id
  is-sec f y (x , refl .(f x)) (.x , refl .(f x)) (refl .x , refl .(refl (f x)))
    = refl (refl x , refl (refl (f x)))

  is-retr :  {A : UU l₁} {B : UU l₂}
    → (f : A → B) (y : B) (xp xp' : fib f y)
    → Eq-fib→≡ f y xp xp' ∘ ≡→Eq-fib f y xp xp' ~ id
  is-retr f y (x , refl .(f x)) (.x , refl .(f x)) (refl (.x , refl .(f x)))
    = refl (refl (x , refl (f x)))

is-contrᶠ : {A : UU l₁} {B : UU l₂}
  → (A → B) → UU (l₁ ⊔ l₂)
is-contrᶠ f = (b : _) → is-contr (fib f b)

{-
is-contrᶠ-is-equiv : {A : UU l₁} {B : UU l₂}
  → (f : A → B)
  → is-contrᶠ f → is-equiv f
is-contrᶠ-is-equiv {A = A} {B = B} f is-contrᶠ-f
  = {!!} , {!!}
  where
    df : (y : B) → fib f y
    df y = center (is-contrᶠ-f y)

    g : B → A
    g = {!!}

-}

-- 10.4 Equivalences are contractible maps
