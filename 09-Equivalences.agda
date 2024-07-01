module 09-Equivalences where

open import 08-Decidability public

-- 9.1 Homotopies

infix  4 _~_
_~_ : {A : UU l₁} {B : A → UU l₂}
  → (f g : (x : A) → B x) → UU (l₁ ⊔ l₂)
f ~ g = (x : _) → f x ≡ g x

neg-neg-bool : neg-bool ∘ neg-bool ~ id
neg-neg-bool false = refl false
neg-neg-bool true  = refl true

refl-htpy : {A : UU l₁} {B : A → UU l₂} {f : (x : A) → B x}
  → f ~ f
refl-htpy x = refl _

inv-htpy : {A : UU l₁} {B : A → UU l₂} {f g : (x : A) → B x}
  → f ~ g → g ~ f
inv-htpy H x = inv (H x)

concat-htpy : {A : UU l₁} {B : A → UU l₂} {f g h : (x : A) → B x}
  → f ~ g → g ~ h → f ~ h
concat-htpy H K x = H x ∙ K x

_∙ᴴ_ = concat-htpy

assoc-htpy : {A : UU l₁} {B : A → UU l₂} {f g h s : (x : A) → B x}
  → (H : f ~ g) (K : g ~ h) (L : h ~ s)
  → (H ∙ᴴ K) ∙ᴴ L ~ H ∙ᴴ (K ∙ᴴ L)
assoc-htpy H K L x = assoc (H x) (K x) (L x)

left-unit-htpy : {A : UU l₁} {B : A → UU l₂}
  → {f g : (x : A) → B x}
  → (H : f ~ g)
  → refl-htpy ∙ᴴ H ~ H
left-unit-htpy H x = left-unit (H x)

right-unit-htpy : {A : UU l₁} {B : A → UU l₂}
  → {f g : (x : A) → B x}
  → (H : f ~ g)
  → H ∙ᴴ refl-htpy ~ H
right-unit-htpy H x = right-unit (H x)

left-inv-htpy : {A : UU l₁} {B : A → UU l₂} {f g : (x : A) → B x}
  → (H : f ~ g)
  → inv-htpy H ∙ᴴ H ~ refl-htpy
left-inv-htpy H x = left-inv (H x)

right-inv-htpy : {A : UU l₁} {B : A → UU l₂} {f g : (x : A) → B x}
  → (H : f ~ g)
  → H ∙ᴴ inv-htpy H ~ refl-htpy
right-inv-htpy H x = right-inv (H x)

left-whisk : {A : UU l₁} {B : UU l₂} {C : UU l₃} {f g : A → B}
  → (h : B → C) (H : f ~ g)
  → h ∘ f ~ h ∘ g
left-whisk h H x = ap h (H x)

_∙l_ = left-whisk

right-whisk : {A : UU l₁} {B : UU l₂} {C : UU l₃} {g h : B → C}
  → (H : g ~ h) (f : A → B)
  → g ∘ f ~ h ∘ f
right-whisk H f x = H (f x)

_∙r_ = right-whisk

-- 9.2 Bi-invertible maps

sec : {A : UU l₁} {B : UU l₂}
  → (A → B) → UU (l₁ ⊔ l₂)
sec f = Σ g ∶ _ , (f ∘ g ~ id)

retr : {A : UU l₁} {B : UU l₂}
  → (A → B) → UU (l₁ ⊔ l₂)
retr f = Σ h ∶ _ , (h ∘ f ~ id)

is-equiv : {A : UU l₁} {B : UU l₂}
  → (A → B) → UU (l₁ ⊔ l₂)
is-equiv f = sec f × retr f

infix  1 _≃_
_≃_ : UU l₁ → UU l₂ → UU (l₁ ⊔ l₂)
A ≃ B = Σ f ∶ (A → B) , is-equiv f

infix  1 _≄_
_≄_ : UU l₁ → UU l₂ → UU (l₁ ⊔ l₂)
A ≄ B = ¬ (A ≃ B)

neg-bool-is-equiv : is-equiv neg-bool
neg-bool-is-equiv
  = (neg-bool , neg-neg-bool) , (neg-bool , neg-neg-bool)

has-inverse : {A : UU l₁} {B : UU l₂}
  → (f : A → B) → UU (l₁ ⊔ l₂)
has-inverse f
  = Σ g ∶ _ , (f ∘ g ~ id × g ∘ f ~ id)

has-inverse→is-equiv : {A : UU l₁} {B : UU l₂}
  → {f : A → B} → has-inverse f → is-equiv f
has-inverse→is-equiv (g , H , K)
  = (g , H) , (g , K)

is-equiv→has-inverse : {A : UU l₁} {B : UU l₂}
  → (f : A → B) → is-equiv f → has-inverse f
is-equiv→has-inverse f ((g , G) , (h , H))
  = g , (G , (K ∙r f) ∙ᴴ H)
  where
  K : g ~ h
  K = inv-htpy (H ∙r g) ∙ᴴ (h ∙l G)

refl-equiv : {A : UU l₁}
  → A ≃ A
refl-equiv = id , (id , refl) , (id , refl)

inv-equiv : {A : UU l₁} {B : UU l₂}
  → A ≃ B → B ≃ A
inv-equiv (f , (g , G) , (h , H))
  = g , (f , pr₂ (pr₂ K)) , (f , G)
  where
    K : has-inverse f
    K = is-equiv→has-inverse f ((g , G) , (h , H))

Φ⊎B≃B : {B : UU l₁}
  → Φ ⊎ B ≃ B
Φ⊎B≃B
  = [ ex-falso , id ]
  , (inr , refl)
  , (inr , λ{ (inr x) → refl (inr x) })

A⊎B≃B : {A : UU l₁} {B : UU l₂}
  → A ⊎ B ≃ B ⊎ A
A⊎B≃B
  = [ inr , inl ]
  , ([ inr , inl ] , λ{ (inl x) → refl (inl x) ; (inr x) → refl (inr x) })
  , ([ inr , inl ] , λ{ (inl x) → refl (inl x) ; (inr x) → refl (inr x) })

ΣΦB≃Φ : {B : Φ → UU l₁}
  → Σ x ∶ Φ , B x ≃ Φ
ΣΦB≃Φ
  = (λ{ (() , _) })
  , ((λ ()) , λ ())
  , ((λ ()) , λ{ (() , _) })

ΣAΦ≃Φ : {A : UU l₁}
  → Σ x ∶ A , Φ ≃ Φ
ΣAΦ≃Φ
  = (λ{ (_ , ()) })
  , ((λ ()) , λ ())
  , ((λ ()) , λ{ (_ , ()) })

Σ𝟏B≃B : {B : 𝟏 → UU l₁}
  → Σ x ∶ 𝟏 , B x ≃ B ＊
Σ𝟏B≃B
  = (λ{ (＊ , y) → y })
  , ((λ y → (＊ , y)) , refl)
  , ((λ y → (＊ , y)) , λ{ (＊ , y) → refl (＊ , y) })

ΣA𝟏≃A : {A : UU l₁}
  → Σ x ∶ A , 𝟏 ≃ A
ΣA𝟏≃A
  = pr₁
  , ((λ x → (x , ＊)) , refl)
  , ((λ x → (x , ＊)) , λ{ (x , ＊) → refl (x , ＊) })

Σ-assoc1 : {A : UU l₁} {B : A → UU l₁} {C : Σ x ∶ A , B x → UU l₃}
  → Σ w ∶ (Σ x ∶ A , B x) , C w ≃ Σ x ∶ A , Σ y ∶ B x , C (x , y)
Σ-assoc1
  = (λ{ ((x , y) , z) → (x , (y , z)) })
  , ((λ{ (x , (y , z)) → ((x , y) , z) }) , λ{ (x , (y , z)) → refl (x , (y , z)) })
  , ((λ{ (x , (y , z)) → ((x , y) , z) }) , λ{ ((x , y) , z) → refl ((x , y) , z) })

Σ-assoc2 : {A : UU l₁} {B : A → UU l₁} {C : (x : A) → B x → UU l₃}
  → Σ w ∶ (Σ x ∶ A , B x) , C (pr₁ w) (pr₂ w) ≃ Σ x ∶ A , Σ y ∶ B x , C x y
Σ-assoc2
  = (λ{ ((x , y) , z) → (x , (y , z)) })
  , ((λ{ (x , (y , z)) → ((x , y) , z) }) , λ{ (x , (y , z)) → refl (x , (y , z)) })
  , ((λ{ (x , (y , z)) → ((x , y) , z) }) , λ{ ((x , y) , z) → refl ((x , y) , z) })

Σ-distr1 : {A : UU l₁} {B : A → UU l₂} {C : A → UU l₃}
  → Σ x ∶ A , (B x ⊎ C x) ≃ Σ x ∶ A , B x ⊎ Σ x ∶ A , C x
Σ-distr1
  = (λ{ (x , inl y) → inl (x , y) ; (x , inr z) → inr (x , z) })
  , ((λ{ (inl (x , y)) → (x , inl y) ; (inr (x , z)) → (x , inr z) })
    , λ{ (inl (x , y)) → refl (inl (x , y)) ; (inr (x , z)) → refl (inr (x , z)) }
    )
  , ((λ{ (inl (x , y)) → (x , inl y) ; (inr (x , z)) → (x , inr z) })
    , λ{ (x , inl y) → refl (x , inl y) ; (x , inr z) → refl (x , inr z) }
    )

Σ-distr2 : {A : UU l₁} {B : UU l₂} {C : A ⊎ B → UU l₃}
  → Σ w ∶ A ⊎ B , C w ≃ Σ x ∶ A , C (inl x) ⊎ Σ y ∶ B , C (inr y)
Σ-distr2
  = (λ{ (inl x , z) → inl (x , z) ; (inr y , z) → inr (y , z) })
  , ((λ{ (inl (x , z)) → (inl x , z) ; (inr (y , z)) → (inr y , z) })
    , λ{ (inl (x , z)) → refl (inl (x , z)) ; (inr (y , z)) → refl (inr (y , z)) }
    )
  , ((λ{ (inl (x , z)) → (inl x , z) ; (inr (y , z)) → (inr y , z) })
    , λ{ (inl x , z) → refl (inl x , z) ; (inr y , z) → refl (inr y , z) }
    )

-- 9.3 Characterizing the identity types of Σ-types

EqΣ : {A : UU l₁} {B : A → UU l₂}
  → Σ x ∶ A , (B x)
  → Σ x ∶ A , (B x)  
  → UU (l₁ ⊔ l₂)
EqΣ (a , b) (a' , b')
  = Σ α ∶ a ≡ a' , (tr _ α b ≡ b')

refl-EqΣ : {A : UU l₁} {B : A → UU l₂}
  → (s : Σ x ∶ A , B x) → EqΣ s s
refl-EqΣ = indΣ f
  where
  f : (x : _) (y : _) → Σ α ∶ (x ≡ x) , (tr _ α y ≡ y)
  f x y = refl x , refl y

pair-eq : {A : UU l₁} {B : A → UU l₂}
  → (s t : Σ x ∶ A , B x)
  → s ≡ t → EqΣ s t
pair-eq s .s (refl .s) = refl-EqΣ s

≡→EqΣ = pair-eq

eq-pair : {A : UU l₁} {B : A → UU l₂}
  → (s t : Σ x ∶ A , B x)
  → EqΣ s t → s ≡ t
eq-pair (x , y) (x' , y') = indΣ f
  where
  f : (p : x ≡ x') → tr _ p y ≡ y' → (x , y) ≡ (x' , y')
  f (refl .x) (refl .y) = refl (x , y)

EqΣ→≡ = eq-pair

pair-eq-is-sec : {A : UU l₁} {B : A → UU l₂}
  → (s t : Σ x ∶ A , B x)
  → sec (pair-eq s t)
pair-eq-is-sec (x , y) (x' , y')
  = eq-pair (x , y) (x' , y')
  , λ{ ((refl .x) , (refl .y)) → refl (refl x , refl y) }

pair-eq-isʳetr : {A : UU l₁} {B : A → UU l₂}
  → (s t : Σ x ∶ A , B x)
  → retr (pair-eq s t)
pair-eq-isʳetr (x , y) (x' , y')
  = eq-pair (x , y) (x' , y')
  , λ{ (refl .(x , y)) → refl (refl (x , y)) }

pair-eq-is-equiv : {A : UU l₁} {B : A → UU l₂}
  → (s t : Σ x ∶ A , B x)
  → is-equiv (pair-eq s t)
pair-eq-is-equiv s t = pair-eq-is-sec s t , pair-eq-isʳetr s t

-- Exercises

inv-is-equiv : {A : UU l₁} {x y : A}
  → is-equiv (inv {x = x} {y = y})
inv-is-equiv
  = (inv , λ{ (refl x) → refl (refl x) })
  , (inv , λ{ (refl x) → refl (refl x) })

concat-is-equiv : {A : UU l₁} {x y z : A}
  → (p : x ≡ y) → is-equiv (concat {z = z} p)
concat-is-equiv (refl x)
  = (id , λ{ (refl x) → refl (refl x) })
  , (id , λ{ (refl x) → refl (refl x) })

concat' : {A : UU l₁} {x y z : A}
  → y ≡ z → x ≡ y → x ≡ z
concat' = swap concat

concat'-is-equiv : {A : UU l₁} {x y z : A}
  → (q : y ≡ z) → is-equiv (concat' {x = x} q)
concat'-is-equiv (refl x)
  = (id , λ{ (refl x) → refl (refl x) })
  , (id , λ{ (refl x) → refl (refl x) })

tr-is-equiv : {A : UU l₁} (B : A → UU l₂) {x y : A}
  → (p : x ≡ y) → is-equiv (tr B p)
tr-is-equiv B (refl x)
  = (tr B (inv (refl x)) , λ Bx → refl Bx)
  , (tr B (inv (refl x)) , λ Bx → refl Bx)

constb-is-not-equiv :
  (b : bool) → ¬ is-equiv (const {A = bool} b)
constb-is-not-equiv false ((s , is-sec) , r-isʳetr)
  = f≢t (is-sec true)
constb-is-not-equiv true  ((s , is-sec) , r-isʳetr)
  = f≢t (inv (is-sec false))

postulate
  bool≄𝟏 : bool ≄ 𝟏

  ℕ≄Fin : {k : ℕ}
    → ℕ ≄ Fin k


9-3a : {A : UU l₁} {B : UU l₂}
  → (f g : A → B) (H : f ~ g)
  → is-equiv f ↔ is-equiv g
9-3a f g H = to , from
  where
  to : is-equiv f → is-equiv g
  to ((s , is-sec) , (r , isʳetr))
    = (s , (inv-htpy (H ∙r s) ∙ᴴ is-sec))
    , (r , ((r ∙l (inv-htpy H)) ∙ᴴ isʳetr))
  from : is-equiv g → is-equiv f
  from ((s , is-sec) , (r , isʳetr))
    = (s , ((H ∙r s) ∙ᴴ is-sec))
    , (r , ((r ∙l H) ∙ᴴ isʳetr))

9-4a : {A : UU l₁} {B : UU l₂} {X : UU l₃}
  → (f : A → X) (g : B → X) (h : A → B)
    (H : f ~ g ∘ h) (sec-s : sec h)
  → g ~ f ∘ (pr₁ sec-s)
9-4a f g h H (s , is-sec) = inv-htpy ((H ∙r s) ∙ᴴ (g ∙l is-sec))

9-4b : {A : UU l₁} {B : UU l₂} {X : UU l₃}
  → (f : A → X) (g : B → X) (h : A → B)
    (H : f ~ g ∘ h) (retrʳ : retr g)
  → h ~ (pr₁ retrʳ) ∘ f
9-4b f g h H (r , isʳetr) = inv-htpy ((r ∙l H) ∙ᴴ (isʳetr ∙r h))

Σ-swap1 : {A : UU l₁} {B : UU l₂} {C : A → B → UU l₃}
  → Σ x ∶ A , Σ y ∶ B , C x y ≃ Σ y ∶ B , Σ x ∶ A , C x y
Σ-swap1
  = (λ{ (x , y , z) → (y , x , z) })
  , ((λ{ (y , x , z) → (x , y , z) }) , λ{ (y , x , z) → refl (y , x , z)})
  , ((λ{ (y , x , z) → (x , y , z) }) , λ{ (y , x , z) → refl (y , x , z)})

Σ-swap2 : {A : UU l₁} {B : A → UU l₂} {C : A → UU l₃}
  → Σ u ∶ (Σ x ∶ A , B x) , C (pr₁ u) ≃ Σ v ∶ (Σ x ∶ A , C x) , B (pr₁ v)
Σ-swap2 = (λ{ ((x , Bx) , Cx) → ((x , Cx) , Bx) })
  , ((λ{ ((x , Cx) , Bx) → ((x , Bx) , Cx) }) , λ{ ((x , Cx) , Bx) → refl ((x , Cx) , Bx) })
  , ((λ{ ((x , Cx) , Bx) → ((x , Bx) , Cx) }) , λ{ ((x , Cx) , Bx) → refl ((x , Cx) , Bx) })

id⊎id~id⊎ : {A : UU l₁} {B : UU l₂}
  → id ⊎ᶠ id ~ id {A = A ⊎ B}
id⊎id~id⊎ (inl x) = refl (inl x)
id⊎id~id⊎ (inr y) = refl (inr y)

∘⊎∘~⊎∘⊎ : 
  {A : UU l₁} {A' : UU l₂} {A'' : UU l₃}
  → {B : UU l₄} {B' : UU l₅} {B'' : UU l₆}
  → (f : A → A') (f' : A' → A'')
  → (g : B → B') (g' : B' → B'')
  → (f' ∘ f) ⊎ᶠ (g' ∘ g) ~ (f' ⊎ᶠ g') ∘ (f ⊎ᶠ g)
∘⊎∘~⊎∘⊎ f f' g g' (inl x) = refl (inl (f' (f x)))
∘⊎∘~⊎∘⊎ f f' g g' (inr y) = refl (inr (g' (g y)))

_⊎ᴴ_ : {A : UU l₁} {A' : UU l₂}
  → {B : UU l₃} {B' : UU l₄}
  → {f f' : A → A'}{g g' : B → B'}
  → (H : f ~ f') (K : g ~ g')
  → f ⊎ᶠ g ~ f' ⊎ᶠ g'
(H ⊎ᴴ K) (inl x) = ap inl (H x)
(H ⊎ᴴ K) (inr y) = ap inr (K y)

{-
⊎ᶠ-is-equiv : {A : UU l₁} {A' : UU l₂}
  → {B : UU l₃} {B' : UU l}
  → (f : A → A') (g : B → B')
  → is-equiv f → is-equiv g
  → is-equiv (f ⊎ᶠ g)
⊎ᶠ-is-equiv {i} {j} {k} {l} f g
  ((fs , fs-is-sec) , (fr , fr-isʳetr))
  ((gs , gs-is-sec) , (gr , gr-isʳetr))
  = (fs ⊎ᶠ gs , {!!})
  , (fr ⊎ᶠ gr , {!!})
-}

_×ᶠ_ : {A : UU l₁} {A' : UU l₂}
  → {B : UU l₃} {B' : UU l₄}
  → (f : A → A') (g : B → B')
  → A × B → A' × B'
(f ×ᶠ g) (a , b) = f a , g b

id×ᶠid~id×ᶠ : {A : UU l₁} {B : UU l₂}
  → id {A = A} ×ᶠ id {A = B} ~ id {A = A × B}
id×ᶠid~id×ᶠ (a , b) = refl (a , b)

∘×ᶠ∘~×ᶠ∘×ᶠ :
  {A : UU l₁} {A' : UU l₂} {A'' : UU l₃}
  → {B : UU l₃} {B' : UU l₅} {B'' : UU l₆}
  → (f : A → A') (f' : A' → A'')
  → (g : B → B') (g' : B' → B'')
  → (f' ∘ f) ×ᶠ (g' ∘ g) ~ (f' ×ᶠ g') ∘ (f ×ᶠ g)
∘×ᶠ∘~×ᶠ∘×ᶠ f f' g g' (a , b) = refl (f' (f a) , g' (g b))

Eq× :  {A : UU l₁} {B : UU l₂}
  → (x y : A × B)
  → UU (l₁ ⊔ l₂)
Eq× (a , b) (a' , b') = a ≡ a' × b ≡ b'

Eq×→≡ : {A : UU l₁} {B : UU l₂}
  → (x y : A × B)
  → Eq× x y → x ≡ y
Eq×→≡ (x , x₁) (.x , .x₁) (refl .x , refl .x₁) = refl (x , x₁)

_×ᴴ_ : {A : UU l₁} {A' : UU l₂}
  → {B : UU l₃} {B' : UU l₄}
  → {f f' : A → A'} {g g' : B → B'}
  → (H : f ~ f') (K : g ~ g')
  → f ×ᶠ g ~ f' ×ᶠ g'
_×ᴴ_ {f = f} {f'} {g} {g'} H K (a , b) = Eq×→≡ (f a , g b) (f' a , g' b) (H a , K b)

{-
Fin+≃Fin⊎Fin : {k l : ℕ}
  → Fin (k + l) ≃ Fin k ⊎ Fin l
Fin+≃Fin⊎Fin {k} {l}
  = to
  , (from , {!!})
  , (from , {!!})
  where
    to : {k l : ℕ}
      → Fin (k + l) → Fin k ⊎ Fin l
    to {l = 0ℕ} x = inl x
    to {l = succℕ l} pt = inr pt
    to {l = succℕ l} (𝓲 x) = (id ⊎ᶠ 𝓲) (to {l = l} x) 

    from : {k l : ℕ}
      → Fin k ⊎ Fin l → Fin (k + l)
    from {l = 0ℕ} (inl x) = x
    from {l = succℕ l} (inl pt) = pt
    from {l = succℕ l} (inl (𝓲 x)) = 𝓲 (from {l = l} (inl (𝓲 x)))
    from {k} {l = succℕ l} (inr pt) = 𝓲 (from {l = l} ({!pt!}))
    from {l = succℕ l} (inr (𝓲 x)) = {!!}
    
{-
    from : {k l : ℕ}
      → Fin k ⊎ Fin l → Fin (k + l)
    from {l = 0ℕ} (inl x) = x
    from {l = succℕ l} (inl x) = 𝓲 (from {l = l} (inl x))
    from {l = succℕ l} (inr pt) = pt
    from {l = succℕ l} (inr (𝓲 x)) = 𝓲 (from {l = l} (inr x))
-}
{-
    to∘from~id : {k l : ℕ}
      → to {k} {l} ∘ from ~ id
    to∘from~id {k} {0ℕ} (inl x) = refl (inl x)
    to∘from~id {k} {succℕ l} (inl x) = {!!}
    to∘from~id {k} {succℕ l} (inr pt) = refl (inr pt)
    to∘from~id {k} {succℕ l} (inr (𝓲 x)) = {!to∘from~id {k} {l} (inr x)!}
-}
-}
