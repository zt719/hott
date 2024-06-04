module 09-Equivalences where

open import 08-Decidability public

-- 9.1 Homotopies

_~_ : {A : UU i} {B : A → UU j}
  → (f g : (x : A) → B x) → UU (i ⊔ j)
f ~ g = (x : _) → f x ≡ g x
infix  4 _~_

_≁_ : {A : UU i} {B : A → UU j}
  → (f g : (x : A) → B x) → UU (i ⊔ j)
f ≁ g = ¬ (f ~ g)

neg-neg-bool : neg-bool ∘ neg-bool ~ id bool
neg-neg-bool false = refl false
neg-neg-bool true  = refl true

-- homotopies between homotopies
_~~_ : {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  → (H K : f ~ g) → UU (i ⊔ j)
H ~~ K = (x : _) → H x ≡ K x

refl-htpy : {A : UU i} {B : A → UU j} {f : (x : A) → B x}
  → f ~ f
refl-htpy x = refl _

inv-htpy : {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  → f ~ g → g ~ f
inv-htpy H x = H x ⁻¹

concat-htpy : {A : UU i} {B : A → UU j} {f g h : (x : A) → B x}
  → f ~ g → g ~ h → f ~ h
concat-htpy H K x = H x ∙ K x

_∙h_ = concat-htpy

assoc-htpy : {A : UU i} {B : A → UU j} {f g h s : (x : A) → B x}
  → (H : f ~ g) (K : g ~ h) (L : h ~ s)
  → (H ∙h K) ∙h L ~ H ∙h (K ∙h L)
assoc-htpy H K L x = assoc (H x) (K x) (L x)

left-unit-htpy : {A : UU i} {B : A → UU j}
  → {f g : (x : A) → B x}
  → (H : f ~ g)
  → refl-htpy ∙h H ~ H
left-unit-htpy H x = left-unit (H x)

right-unit-htpy : {A : UU i} {B : A → UU j}
  → {f g : (x : A) → B x}
  → (H : f ~ g)
  → H ∙h refl-htpy ~ H
right-unit-htpy H x = right-unit (H x)

left-inv-htpy : {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  → (H : f ~ g)
  → inv-htpy H ∙h H ~ refl-htpy
left-inv-htpy H x = left-inv (H x)

right-inv-htpy : {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  → (H : f ~ g)
  → H ∙h inv-htpy H ~ refl-htpy
right-inv-htpy H x = right-inv (H x)

left-whisk : {A : UU i} {B : UU j} {C : UU k} {f g : A → B}
  → (h : B → C) (H : f ~ g)
  → h ∘ f ~ h ∘ g
left-whisk h H x = ap h (H x)

_∙l_ = left-whisk

right-whisk : {A : UU i} {B : UU j} {C : UU k} {g h : B → C}
  → (H : g ~ h) (f : A → B)
  → g ∘ f ~ h ∘ f
right-whisk H f x = H (f x)

_∙r_ = right-whisk

-- 9.2 Bi-invertible maps

sec : {A : UU i} {B : UU j}
  → (A → B) → UU (i ⊔ j)
sec {A = A} {B = B} f = Σ g ∶ (B → A) , (f ∘ g ~ id B)

retr : {A : UU i} {B : UU j}
  → (A → B) → UU (i ⊔ j)
retr {A = A} {B = B} f = Σ h ∶ (B → A) , (h ∘ f ~ id A)

is-equiv : {A : UU i} {B : UU j}
  → (A → B) → UU (i ⊔ j)
is-equiv f = sec f × retr f

_≃_ : UU i → UU j → UU (i ⊔ j)
A ≃ B = Σ f ∶ (A → B) , is-equiv f

infix 4 _≃_

_≄_ : UU i → UU j → UU (i ⊔ j)
A ≄ B = ¬ (A ≃ B)

neg-bool-is-equiv : is-equiv neg-bool
neg-bool-is-equiv
  = (neg-bool , neg-neg-bool) , (neg-bool , neg-neg-bool)

has-inverse : {A : UU i} {B : UU j}
  → (f : A → B) → UU (i ⊔ j)
has-inverse {A = A} {B = B} f
  = Σ g ∶ (B → A) , (f ∘ g ~ id B × g ∘ f ~ id A)

has-inverse→is-equiv : {A : UU i} {B : UU j}
  → {f : A → B} → has-inverse f → is-equiv f
has-inverse→is-equiv (g , (H , K))
  = (g , H) , (g , K)

is-equiv→has-inverse : {A : UU i} {B : UU j}
  → (f : A → B) → is-equiv f → has-inverse f
is-equiv→has-inverse f ((g , G) , (h , H))
  = g , (G , (K ∙r f) ∙h H)
  where
  K : g ~ h
  K = (inv-htpy (H ∙r g)) ∙h (h ∙l G)


refl-equiv : {A : UU i}
  → A ≃ A
refl-equiv {A = A} = (id A) , (((id A) , refl) , ((id A) , refl))

{-
inv-equiv : {A : UU i} {B : UU j}
  → A ≃ B → B ≃ A
inv-equiv (f , (g , G) , (h , H)) = g , (f , {!!}) , {!!}
-}

-- 9.3 Characterizing the identity types of Σ-types

EqΣ : {A : UU i} {B : A → UU j}
  → Σ x ∶ A , (B x)
  → Σ x ∶ A , (B x)
  → UU (i ⊔ j)
EqΣ {B = B} s t = Σ α ∶ (pr₁ s ≡ pr₁ t) , (tr B α (pr₂ s) ≡ pr₂ t)

reflexive-EqΣ : {A : UU i} {B : A → UU j}
  → (s : Σ x ∶ A , B x) → EqΣ s s
reflexive-EqΣ = indΣ f
  where
  f : {A : UU i} {B : A → UU j}
    → (x : A) (y : B x)
    → Σ α ∶ (x ≡ x) , (tr B α y ≡ y)
  f x y = (refl x , refl y)

pair-eq : {A : UU i} {B : A → UU j}
  → (s t : Σ x ∶ A , B x)
  → s ≡ t → EqΣ s t
pair-eq s .s (refl .s) = reflexive-EqΣ s

eq-pair : {A : UU i} {B : A → UU j}
  → (s t : Σ x ∶ A , B x)
  → EqΣ s t → s ≡ t
eq-pair {B = B} (x , y) (x′ , y′) = indΣ f
  where
  f : (p : x ≡ x′) → tr B p y ≡ y′ → (x , y) ≡ (x′ , y′)
  f (refl .x) (refl .y) = refl (x , y)

pair-eq-is-sec : {A : UU i} {B : A → UU j}
  → (s t : Σ x ∶ A , B x)
  → sec (pair-eq s t)
pair-eq-is-sec {B = B} (x , y) (x′ , y′)
  = eq-pair (x , y) (x′ , y′)
  , λ{ ((refl .x) , (refl .y)) → refl (refl x , refl y) }

pair-eq-is-retr : {A : UU i} {B : A → UU j}
  → (s t : Σ x ∶ A , B x)
  → retr (pair-eq s t)
pair-eq-is-retr (x , y) (x′ , y′)
  = eq-pair (x , y) (x′ , y′)
  , λ{ (refl .(x , y)) → refl (refl (x , y)) }

pair-eq-is-equiv : {A : UU i} {B : A → UU j}
  → (s t : Σ x ∶ A , B x)
  → is-equiv (pair-eq s t)
pair-eq-is-equiv s t = pair-eq-is-sec s t , pair-eq-is-retr s t

-- Exercises
-- 9.1

inv′ : {A : UU i}
  → (x y : A)
  → x ≡ y → y ≡ x
inv′ x .x (refl .x) = refl x

inv-is-sec : {A : UU i}
  → (x y : A) → sec (inv′ x y)
inv-is-sec x y = inv , (λ{ (refl .x) → refl (refl x)} )

inv-is-retr : {A : UU i}
  → (x y : A) → retr (inv′ x y)
inv-is-retr x y = inv , (λ{ (refl .x) → refl (refl x)} )

inv-is-equiv : {A : UU i}
  → (x y : A) → is-equiv (inv′ x y)
inv-is-equiv x y = (inv-is-sec x y) , (inv-is-retr x y)

concat′ : {A : UU i}
  → (x y z : A) → x ≡ y → y ≡ z → x ≡ z
concat′ x .x .x (refl .x) (refl .x) = refl x

concat-is-sec : {A : UU i}
  → (x y z : A) (p : x ≡ y) → sec (concat′ x y z p)
concat-is-sec x .x z (refl .x)
  = id (x ≡ z) , λ{ (refl .x) → refl (refl x) }

concat-is-retr : {A : UU i}
  → (x y z : A) (p : x ≡ y) → retr (concat′ x y z p)
concat-is-retr x .x z (refl .x)
  = id (x ≡ z) , λ{ (refl .x) → refl (refl x) }

tr-is-sec : {A : UU i} (B : A → UU j)
  → (x y : A) (p : x ≡ y) → sec (tr B p)
tr-is-sec B x .x (refl .x)
  = tr B (inv (refl x)) , λ Bx → refl Bx

tr-is-retr : {A : UU i} (B : A → UU j)
  → (x y : A) (p : x ≡ y) → retr (tr B p)
tr-is-retr B x .x (refl .x)
  = tr B (inv (refl x)) , λ Bx → refl Bx

tr-is-equiv : {A : UU i} (B : A → UU j)
  → (x y : A) (p : x ≡ y) → is-equiv (tr B p)
tr-is-equiv B x y p = (tr-is-sec B x y p) , (tr-is-retr B x y p)


constb : bool → bool → bool
constb b _ = b

t≢f : true ≢ false
t≢f = λ ()

constb-is-not-equiv :
  (b : bool) → ¬ is-equiv (constb b)
constb-is-not-equiv false ((s , is-sec) , (r , is-retr))
  = t≢f (inv (is-sec true))
constb-is-not-equiv true  ((s , is-sec) , (r , is-retr))
  = t≢f (is-sec false)

-- 9.3

9-3a : {A : UU i} {B : UU j}
  → (f g : A → B) (H : f ~ g)
  → is-equiv f ↔ is-equiv g
9-3a f g H = to , from
  where
  to : is-equiv f → is-equiv g
  to ((s , is-sec) , (r , is-retr))
    = (s , (inv-htpy (H ∙r s) ∙h is-sec))
    , (r , ((r ∙l (inv-htpy H)) ∙h is-retr))
  from : is-equiv g → is-equiv f
  from ((s , is-sec) , (r , is-retr))
    = (s , ((H ∙r s) ∙h is-sec))
    , (r , ((r ∙l H) ∙h is-retr))

-- 9.4

9-4a : {A : UU i} {B : UU j} {X : UU k}
  → (f : A → X) (g : B → X) (h : A → B)
    (H : f ~ g ∘ h) (sec-s : sec h)
  → g ~ f ∘ (pr₁ sec-s)
9-4a f g h H (s , is-sec) = inv-htpy ((H ∙r s) ∙h (g ∙l is-sec))

9-4b : {A : UU i} {B : UU j} {X : UU k}
  → (f : A → X) (g : B → X) (h : A → B)
    (H : f ~ g ∘ h) (retr-r : retr g)
  → h ~ (pr₁ retr-r) ∘ f
9-4b f g h H (r , is-retr) = inv-htpy ((r ∙l H) ∙h (is-retr ∙r h))

 
