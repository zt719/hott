module 10-Contractible-Types where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
open import 09-Equivalences public

private variable 𝓲 𝓳 𝓴 : Level

-- 10.1 Contractible types

is-contr : Π[ A ∶ 𝓤 𝓲 ] 𝓤 𝓲
is-contr A = Σ[ c ∶ A ] Π[ x ∶ A ] (c ≡ x)

center : {A : 𝓤 𝓲}
  → Π[ a ∶ is-contr A ] A
center (c , C) = c

contraction : {A : 𝓤 𝓲}
  → Π[ a ∶ is-contr A ] (const (center a) ~ id A)
contraction (c , C) = C

𝟙-is-contr : is-contr 𝟙
𝟙-is-contr = (＊ , ind𝟙 (refl ＊))

Σ≡-is-contr : {A : 𝓤 𝓲}
  → Π[ a ∶ A ] is-contr (Σ[ x ∶ A ] (a ≡ x))
Σ≡-is-contr a = ((a , refl a) , unique-refl a)

is-contr-is-equiv-to-𝟙 : {A : 𝓤 𝓲}
  → is-contr A
  → is-equiv (const ＊)
is-contr-is-equiv-to-𝟙 (c , C)
  = (const c , contraction 𝟙-is-contr)
  , (const c , C)

is-equiv-to-𝟙-is-contr : {A : 𝓤 𝓲}
  → is-equiv (const {A = A} ＊)
  → is-contr A
is-equiv-to-𝟙-is-contr ((s , is-sec) , (retr , is-retr))
  = (retr ＊ , is-retr)

-- 10.2 Singleton induction

-- evaluate map at 'a'
ev-pt : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → Π[ a ∶ A ] (Π[ x ∶ A ] B x ⇒ B a)
ev-pt A B a f = f a

sat-sing-ind : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → Π[ a ∶ A ] 𝓤 (𝓲 ⊔ 𝓳)
sat-sing-ind A B a = sec (ev-pt A B a)

ind-sing : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → (a : A)
  → sat-sing-ind A B a
  → B a ⇒ Π[ x ∶ A ] B x
ind-sing A B a (s , is-sec) = s

comp-sing : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → Π[ a ∶ A ] Π[ ssi ∶ sat-sing-ind A B a ]
    (ev-pt A B a ∘ ind-sing A B a ssi ~ id (B a))
comp-sing A B a (s , is-sec) = is-sec

𝟙-sat-sing-ind : {B : 𝟙 → 𝓤 𝓲}
  → sat-sing-ind 𝟙 B ＊
𝟙-sat-sing-ind = ind𝟙 , (λ a → refl a)

is-contr-sat-sing-ind : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳)
  → is-contr A
  ⇒ Π[ a ∶ A ] sat-sing-ind A B a
is-contr-sat-sing-ind A B (_ , C) a
  = (ind-s , comp-s)
  where
  ind-s : B a ⇒ Π[ x ∶ A ] B x
  ind-s b x = tr B (inv (C a) ∙ C x) b

  comp-s : ev-pt A B a ∘ ind-s ~ id (B a)
  comp-s b = ap (λ ω → tr B ω b) (left-inv (C a))

postulate
  sat-sing-ind-is-contr : (A : 𝓤 𝓲) (B : A → 𝓤 𝓲)
    → Π[ a ∶ A ] (sat-sing-ind A B a ⇒ is-contr A)
  -- sat-sing-ind-is-contr A B a S = a , λ x → {!!}

-- 10.3 Contractible maps

fib : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] Π[ b ∶ B ] 𝓤 (𝓲 ⊔ 𝓳)
fib {A = A} f b = Σ[ a ∶ A ] (f a ≡ b)

Eq-fib : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] Π'[ y ∶ B ] Π[ xp xp′ ∶ fib f y ] 𝓤 (𝓲 ⊔ 𝓳)
Eq-fib f (x , p) (x′ , p′) = Σ[ α ∶ x ≡ x′ ] (p ≡ ap f α ∙ p′)

Eq-fib-reflexive : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] Π'[ y ∶ B ] Π[ xp ∶ fib f y ] Eq-fib f xp xp
Eq-fib-reflexive f (x , refl .(f x)) = ((refl x) , refl (refl (f x)))

≡⇒Eq-fib : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] Π'[ y ∶ B ] Π[ xp xp′ ∶ fib f y ]
    (xp ≡ xp′ ⇒ Eq-fib f xp xp′)
≡⇒Eq-fib f xp .xp (refl .xp) = Eq-fib-reflexive f xp

Eq-fib⇒≡-is-equiv : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] Π'[ y ∶ B ] Π[ xp xp′ ∶ fib f y ]
    (is-equiv (≡⇒Eq-fib f xp xp′))
Eq-fib⇒≡-is-equiv f xp xp′
  = (Eq-fib⇒≡ f xp xp′ , is-sec f xp xp′)
  , (Eq-fib⇒≡ f xp xp′ , is-retr f xp xp′)
  where
  Eq-fib⇒≡ : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
    → Π[ f ∶ A ⇒ B ] Π'[ y ∶ B ] Π[ xp xp′ ∶ fib f y ]
      (Eq-fib f xp xp′ ⇒ xp ≡ xp′)
  Eq-fib⇒≡ f (x , refl .(f x)) (.x , refl .(f x)) (refl .x , refl .(refl (f x)))
    = refl (x , refl (f x))

  is-sec :  {A : 𝓤 𝓲} {B : 𝓤 𝓳}
    → Π[ f ∶ A ⇒ B ] Π'[ y ∶ B ] Π[ xp xp′ ∶ fib f y ]
      (≡⇒Eq-fib f xp xp′ ∘ Eq-fib⇒≡ f xp xp′ ~ id (Eq-fib f xp xp′))
  is-sec f (x , refl .(f x)) (.x , refl .(f x)) (refl .x , refl .(refl (f x)))
    = refl (refl x , refl (refl (f x)))

  is-retr :  {A : 𝓤 𝓲} {B : 𝓤 𝓳}
    → Π[ f ∶ A ⇒ B ] Π'[ y ∶ B ] Π[ xp xp′ ∶ fib f y ]
      (Eq-fib⇒≡ f xp xp′ ∘ ≡⇒Eq-fib f xp xp′ ~ id (xp ≡ xp′))
  is-retr f (x , refl .(f x)) (.x , refl .(f x)) (refl (.x , refl .(f x)))
    = refl (refl (x , refl (f x)))

-- 10.4 Equivalences are contractible maps

is-contr-map : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] 𝓤 (𝓲 ⊔ 𝓳)
is-contr-map {B = B} f = Π[ b ∶ B ] is-contr (fib f b)

{-
is-contr-map-is-equiv : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → Π[ f ∶ A ⇒ B ] (is-contr-map f ⇒ is-equiv f)
is-contr-map-is-equiv {A = A} {B = B} f is-contr-map-f
  = (g , G)
  , (g , {!!})
  where
  df : Π[ y ∶ B ] fib f y
  df y = center (is-contr-map-f y)

  g : B ⇒ A
  g y = pr₁ (df y)

  G : Π[ y ∶ B ] (f (g y) ≡ y)
  G y = pr₂ (df y)

  p : Π[ x ∶ A ] (f (g (f x)) ≡ f x)
  p x = G (f x)

  q : Π[ x ∶ A ] ((g (f x) , p x) ≡ (x , refl (f x)))
  q x = {!is-contr-map-f (f x)!}
-}
