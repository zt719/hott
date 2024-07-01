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

is-contr→≡ : {A : UU l₁}
  → is-contr A
  → (x y : A)
  → x ≡ y
is-contr→≡ (c , C) x y = inv (C x) ∙ C y

𝟏-is-contr : is-contr 𝟏
𝟏-is-contr = ＊ , ind𝟏 (refl ＊)

Σa≡x-is-contr : {A : UU l₁}
  → (a : A)
  → is-contr (Σ x ∶ A , (a ≡ x))
Σa≡x-is-contr a = (a , refl a) , unique-refl a

is-contr→is-equiv-to-𝟏 : {A : UU l₁}
  → is-contr A
  → is-equiv (const ＊)
is-contr→is-equiv-to-𝟏 (c , C)
  = (const c , contraction 𝟏-is-contr)
  , (const c , C)

is-equiv-to-𝟏→is-contr : {A : UU l₁}
  → is-equiv (const ＊)
  → is-contr A
is-equiv-to-𝟏→is-contr ((s , is-sec) , (retr , is-retr))
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
  comp-s b = ap (λ ω → tr B ω b) (left-inv (C a))

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
fib f y = Σ x ∶ _ , (f x ≡ y)

Eq-fib : {A : UU l₁} {B : UU l₂}
  → (f : A → B) (y : B) (xp xp' : fib f y)
  → UU (l₁ ⊔ l₂)
Eq-fib f y (x , p) (x' , p') = Σ α ∶ x ≡ x' , (p ≡ ap f α ∙ p')

Eq-fib-refl : {A : UU l₁} {B : UU l₂} 
  → (f : A → B) (y : B)
  → is-refl-R (Eq-fib f y)
Eq-fib-refl f y (x , refl .(f x)) = refl x , refl (refl (f x))

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

is-contrᶠ→is-equiv : {A : UU l₁} {B : UU l₂}
  → (f : A → B)
  → is-contrᶠ f → is-equiv f
is-contrᶠ→is-equiv {A = A} {B = B} f is-contrᶠ-f
  = (g , G)
  , (g , H )
  where
    df : (y : B) → fib f y
    df y = center (is-contrᶠ-f y)

    g : B → A
    g y = pr₁ (df y)

    G : f ∘ g ~ id
    G y = pr₂ (df y)

    fib-id : (x : A) → fib f (f x)
    fib-id x = g (f x) , G (f x)

    fib-gf : (x : A) → fib f (f x)
    fib-gf x = x , refl (f x)

    H : g ∘ f ~ id
    H x = ap pr₁ (is-contr→≡ (is-contrᶠ-f (f x)) (fib-id x) (fib-gf x))
    
-- 10.4 Equivalences are contractible maps

is-coh-inv : {A : UU l₁} {B : UU l₂}
  → (f : A → B)
  → UU (l₁ ⊔ l₂)
is-coh-inv f
  = Σ g ∶ _ , Σ G ∶ f ∘ g ~ id , Σ H ∶ g ∘ f ~ id , (G ∙r f ~ f ∙l H)

is-coh-inv→is-contr-fib : {A : UU l₁} {B : UU l₂}
  → (f : A → B)
  → (y : B)
  → is-coh-inv f
  → is-contr (fib f y)
is-coh-inv→is-contr-fib f y (g , G , H , K)
  = c-fib , λ{ (x , p) → Eq-fib→≡ f y c-fib (x , p) (df x p)}
  where
  c-fib : fib f y
  c-fib = g y , G y

  K' : (x : _) → G (f x) ≡ ap f (H x) ∙ refl (f x)
  K' = K ∙ᴴ inv-htpy (right-unit-htpy (f ∙l H))
  
  df : (x : _) (p : f x ≡ y) → Eq-fib f y c-fib (x , p)
  df x (refl .(f x)) = H x , K' x

nat-htpy : {A : UU l₁} {B : UU l₂}
  → {f g : A → B}
  → (H : f ~ g)
  → {x y : A}
  → (p : x ≡ y)
  →  ap f p ∙ H y ≡ H x ∙ ap g p
nat-htpy H (refl x) = inv (right-unit-htpy H x)

d10-4-4 : {A : UU l₁}
  → (f : A → A)
  → (H : f ~ id)
  → (x : A)
  →  ap f (H x) ∙ H x ≡ H (f x) ∙ H x
d10-4-4 f H x
  = ap (ap f (H x) ∙_) (refl (H x))
  ∙ nat-htpy H (H x)
  ∙ ap (H (f x) ∙_) (inv (ap-id (H x)))

{-
lem10-4-5 : {A : UU l₁} {B : UU l₂}
  → (f : A → B)
  → (g : B → A)
  → (G : f ∘ g ~ id)
  → (H : g ∘ f ~ id)
  → Σ G' ∶ f ∘ g ~ id , (f ∙l H ~ G' ∙r f)
lem10-4-5 f g G H = G' , K
  where
    G' : f ∘ g ~ id
    G' y = inv (G (f (g y))) ∙ ap f (H (g y)) ∙ G y

    K : f ∙l H ~ G' ∙r f
    K x = {!!}

    hh : (x : _) → H ((g ∘ f) x) ≡ ap (g ∘ f) (H x)
    hh x = d10-4-4 {!g ∘ f!} {!!} {!x!}
-}
{-
is-equiv→is-contrᶠ : {A : UU l₁} {B : UU l₂}
  → (f : A → B)
  → is-equiv f → is-contrᶠ f
is-equiv→is-contrᶠ f ((g , G) , (h , H)) = {!!}
-}
