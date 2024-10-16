
module 10-Contractible-Types where

open import 09-Equivalences public

-- 10.1 Contractible types

is-contr : (A : UU ℓ₁) → UU ℓ₁
is-contr A = Σ[ c ∈ A ] ((x : A) → c ≡ x)

center : {A : UU ℓ₁}
  → is-contr A → A
center (c , C) = c

contraction : {A : UU ℓ₁}
  → (a : is-contr A)
  → const (center a) ~ id
contraction (c , C) = C

is-contr→≡ : {A : UU ℓ₁}
  → is-contr A
  → (x y : A)
  → x ≡ y
is-contr→≡ (c , C) x y = inv (C x) ∙ C y

𝟙-is-contr : is-contr 𝟙
𝟙-is-contr = ＊ , ind𝟙 (refl ＊)

Σ_≡x-is-contr : {A : UU ℓ₁}
  → (a : A)
  → is-contr (Σ[ x ∈ A ] a ≡ x)
Σ a ≡x-is-contr = (a , refl a) , unique-refl a

is-contr→is-equiv-const-＊ : {A : UU ℓ₁}
  → is-contr A
  → is-equiv (const ＊)
is-contr→is-equiv-const-＊ (c , C)
  = (const c , contraction 𝟙-is-contr) , (const c , C)

is-equiv-const-＊→is-contr : {A : UU ℓ₁}
  → is-equiv (const ＊)
  → is-contr A
is-equiv-const-＊→is-contr ((s , is-sec) , (retr , is-retr))
  = retr ＊ , is-retr

-- 10.2 Singleton induction

ev-pt : {A : UU ℓ₁} (a : A) (B : A → UU ℓ₂) → ((x : A) → B x) → B a
ev-pt a B f = f a

sat-sing-ind : (ℓ : Level) (A : UU ℓ₁) → A → UU (ℓ₁ ⊔ lsuc ℓ)
sat-sing-ind ℓ A a = (B : A → UU ℓ) → sec (ev-pt a B)

𝟙-sat-sing-ind : sat-sing-ind ℓ₁ 𝟙 ＊
𝟙-sat-sing-ind B = ind𝟙 , refl

is-contr→sat-sing-ind : {A : UU ℓ₁}
  → is-contr A
  → (a : A)
  → {ℓ : Level}→ sat-sing-ind ℓ A a
is-contr→sat-sing-ind (c , C) a B
  = ind-sing , comp-sing
  where
  ind-sing : B a → (x : _) → B x
  ind-sing b x = tr B (inv (C a) ∙ C x) b

  comp-sing : ev-pt a B ∘ ind-sing ~ id
  comp-sing b = ap (λ ω → tr B ω b) (left-inv (C a))

sat-sing-ind→is-contr : {A : UU ℓ₁}
  → (a : A)
  → ({ℓ : Level} → sat-sing-ind ℓ A a)
  → is-contr A
sat-sing-ind→is-contr a S = ind-sing→is-contr a (λ B → pr₁ (S B))
  where
  ind-sing→is-contr : {A : UU ℓ₁}
    → (a : A)
    → ({ℓ : Level} (B : A → UU ℓ) → B a → (x : A) → B x)
    → is-contr A
  ind-sing→is-contr a S = a , S (a ≡_) (refl a)

-- 10.3 Contractible maps

fib : {A : UU ℓ₁} {B : UU ℓ₂}
  → (A → B) → B → UU (ℓ₁ ⊔ ℓ₂)
fib f y = Σ[ x ∈ _ ] f x ≡ y

Eq-fib : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B) (y : B) (xp xp' : fib f y) → UU (ℓ₁ ⊔ ℓ₂)
Eq-fib f y (x , p) (x' , p') = Σ[ α ∈ x ≡ x' ] p ≡ ap f α ∙ p'

Eq-fib-refl : {A : UU ℓ₁} {B : UU ℓ₂} 
  → (f : A → B) (y : B) (xp : fib f y) → Eq-fib f y xp xp
Eq-fib-refl f y (x , refl .(f x)) = refl x , refl (refl (f x))

≡→Eq-fib : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B) (y : B) (xp xp' : fib f y)
  → xp ≡ xp'
  → Eq-fib f y xp xp'
≡→Eq-fib f y xp .xp (refl .xp) = Eq-fib-refl f y xp

Eq-fib→≡ : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B) (y : B) (xp xp' : fib f y)
  → Eq-fib f y xp xp' → xp ≡ xp'
Eq-fib→≡ f y (x , refl .(f x)) (.x , refl .(f x)) (refl .x , refl .(refl (f x)))
  = refl (x , refl (f x))
  
Eq-fib≃≡ : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B) (y : B) (xp xp' : fib f y)
  → xp ≡ xp' ≃ Eq-fib f y xp xp'
Eq-fib≃≡ f y xp xp'
  = ≡→Eq-fib f y xp xp'
  , (Eq-fib→≡ f y xp xp' , is-sec f y xp xp')
  , (Eq-fib→≡ f y xp xp' , is-retr f y xp xp')
  where
  is-sec :  {A : UU ℓ₁} {B : UU ℓ₂}
    → (f : A → B) (y : B) (xp xp' : fib f y)
    → ≡→Eq-fib f y xp xp' ∘ Eq-fib→≡ f y xp xp' ~ id
  is-sec f y (x , refl .(f x)) (.x , refl .(f x)) (refl .x , refl .(refl (f x)))
    = refl (refl x , refl (refl (f x)))

  is-retr :  {A : UU ℓ₁} {B : UU ℓ₂}
    → (f : A → B) (y : B) (xp xp' : fib f y)
    → Eq-fib→≡ f y xp xp' ∘ ≡→Eq-fib f y xp xp' ~ id
  is-retr f y (x , refl .(f x)) (.x , refl .(f x)) (refl (.x , refl .(f x)))
    = refl (refl (x , refl (f x)))

is-contr-map : {A : UU ℓ₁} {B : UU ℓ₂}
  → (A → B) → UU (ℓ₁ ⊔ ℓ₂)
is-contr-map f = (b : _) → is-contr (fib f b)

is-contr-map→is-equiv : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B) → is-contr-map f → is-equiv f
is-contr-map→is-equiv {A = A} {B = B} f f-is-contr-map
  = (g , G) , (g , H)
  where
  df : (y : B) → fib f y
  df y = center (f-is-contr-map y)

  g : B → A
  g y = pr₁ (df y)

  G : f ∘ g ~ id
  G y = pr₂ (df y)

  fib-gf : (x : A) → fib f (f x)
  fib-gf x = g (f x) , G (f x)

  fib-id : (x : A) → fib f (f x)
  fib-id x = x , refl (f x)

  H : g ∘ f ~ id
  H x = ap pr₁ (is-contr→≡ (f-is-contr-map (f x)) (fib-gf x) (fib-id x))
    
-- 10.4 Equivalences are contractible maps

is-coh-inv : {A : UU ℓ₁} {B : UU ℓ₂}
  → (A → B) → UU (ℓ₁ ⊔ ℓ₂)
is-coh-inv f
  = Σ[ g ∈ _ ] Σ[ G ∈ f ∘ g ~ id ] Σ[ H ∈ g ∘ f ~ id ] G ∙r f ~ f ∙l H

is-coh-inv→is-contr-map : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B)
  → is-coh-inv f → is-contr-map f
is-coh-inv→is-contr-map f (g , G , H , K) y
  = c-fib , contraction-fib
  where
  c-fib : fib f y
  c-fib = g y , G y

  K' : (x : _) → G (f x) ≡ ap f (H x) ∙ refl (f x)
  K' x = K x ∙ inv (right-unit (ap f (H x)))
  
  df : (x : _) (p : f x ≡ y) → Eq-fib f y c-fib (x , p)
  df x (refl .(f x)) = H x , K' x

  contraction-fib : (xp : fib f y) → c-fib ≡ xp
  contraction-fib (x , p) = Eq-fib→≡ f y c-fib (x , p) (df x p)

nat-htpy : {A : UU ℓ₁} {B : UU ℓ₂} {f g : A → B} {x y : A}
  → (H : f ~ g) (p : x ≡ y)
  → ap f p ∙ H y ≡ H x ∙ ap g p
nat-htpy H (refl x) = inv (right-unit-htpy H x)

left-unwhisk : {A : UU ℓ₁} {x y z : A}
  (p : x ≡ y) {q r : y ≡ z} → (p ∙ q) ≡ (p ∙ r) → q ≡ r
left-unwhisk (refl _) s = inv (left-unit _) ∙ s ∙ (left-unit _)

right-unwhisk : {A : UU ℓ₁} {x y z : A}
  → {p q : x ≡ y} (r : y ≡ z) → p ∙ r ≡ q ∙ r → p ≡ q
right-unwhisk (refl _) s = inv (right-unit _) ∙ s ∙ (right-unit _)

htpy-red : {A : UU ℓ₁}
  → (x : A) (f : A → A) (H : f ~ id)
  → H (f x) ≡ ap f (H x)
htpy-red x f H = right-unwhisk (H x) (inv nat-htpy-1)
  where
  nat-htpy-1 : ap f (H x) ∙ H x ≡ H (f x) ∙ H x
  nat-htpy-1
    = ap (ap f (H x) ∙_) (refl (H x))
    ∙ nat-htpy {f = f} {g = id} H (H x)
    ∙ ap (H (f x) ∙_) (inv (ap-id (H x)))

has-inverse→is-coh-inv : {A : UU ℓ₁} {B : UU ℓ₂}
  → (f : A → B) → has-inverse f → is-coh-inv f
has-inverse→is-coh-inv f (g , G , H)
  = g , G′ , H , K
  where
  G′ : f ∘ g ~ id
  G′ y = inv (G (f (g y))) ∙ ap f (H (g y)) ∙ G y

  nat-commute : (x : _) → ap (f ∘ g ∘ f) (H x) ∙ (G ∙r f) x ≡ (G ∙r f) (g (f x)) ∙ ap f (H x)
  nat-commute x = nat-htpy (G ∙r f) (H x)

  commute : (x : _) → ap f (H (g (f x))) ∙ G (f x) ≡ G (f (g (f x))) ∙ ap f (H x)
  commute x
    = ap (_∙ G (f x))
      (ap (ap f) (htpy-red x (g ∘ f) H) ∙ ap-comp (g ∘ f) f (H x))
    ∙ nat-commute x

  move-left : {A : UU ℓ₁} {x y z : A}
    → {p : x ≡ z} (q : x ≡ y) {r : y ≡ z}
    → p ≡ q ∙ r → inv q ∙ p ≡ r
  move-left (refl _) h = h

  commute1 : (x : _) → inv (G (f (g (f x)))) ∙ ap f (H (g (f x))) ∙ G (f x) ≡ ap f (H x)
  commute1 x
    = assoc (inv (G (f (g (f x))))) (ap f (H (g (f x)))) (G (f x))
    ∙ move-left (G (f (g (f x)))) (commute x)

  K : G′ ∙r f ~ f ∙l H
  K x = commute1 x

¬is-contr𝟘 : ¬ (is-contr 𝟘)
¬is-contr𝟘 (c , C) = c

Eqℕ-suc≡𝟘 : (n : ℕ) → Eqℕ n (suc n) ≡ 𝟘
Eqℕ-suc≡𝟘 zero = refl _
Eqℕ-suc≡𝟘 (suc n) = Eqℕ-suc≡𝟘 n

≡𝟘→¬ : {A : UU} → A ≡ 𝟘 → ¬ A
≡𝟘→¬ (refl .𝟘) ()

¬is-contrℕ : ¬ (is-contr ℕ)
¬is-contrℕ (n , p) = ≡𝟘→¬ (Eqℕ-suc≡𝟘 n) (≡→Eqℕ (p (suc n)))

is-contr→≡-is-contr : {A : UU ℓ₁}
  → is-contr A → (x y : A) → is-contr (x ≡ y)
is-contr→≡-is-contr (c , C) x y
  = is-contr→≡ (c , C) x y , λ{ (refl _) → left-inv (C x)}

pr₁-is-equiv↔Ba-is-contr : {A : UU ℓ₁} {B : A → UU ℓ₂}
  → is-contr-map (pr₁ {A = A} {B}) ↔ ((a : A) → is-contr (B a))
pr₁-is-equiv↔Ba-is-contr = {!!}
  
