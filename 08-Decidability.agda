module 08-Decidability where

open import 07-Curry-Howard public

is-decidable : UU ℓ₁ → UU ℓ₁
is-decidable A = A ⊎ ¬ A

𝟙-is-decidable : is-decidable 𝟙
𝟙-is-decidable = inl ＊

𝟘-is-decidable : is-decidable 𝟘
𝟘-is-decidable = inr id

⊎-is-decidable : {A : UU ℓ₁} {B : UU ℓ₂}
  → is-decidable A
  → is-decidable B
  → is-decidable (A ⊎ B)
⊎-is-decidable (inl a) (inl b) = inl (inl a)
⊎-is-decidable (inl a) (inr g) = inl (inl a)
⊎-is-decidable (inr f) (inl b) = inl (inr b)
⊎-is-decidable (inr f) (inr g) = inr [ f , g ]

×-is-decidable : {A : UU ℓ₁} {B : UU ℓ₂}
  → is-decidable A
  → is-decidable B
  → is-decidable (A × B)
×-is-decidable (inl a) (inl b) = inl (a , b)
×-is-decidable (inl a) (inr g) = inr (g ∘ pr₂)
×-is-decidable (inr f) (inl b) = inr (f ∘ pr₁)
×-is-decidable (inr f) (inr g) = inr (f ∘ pr₁)

→-is-decidable : {A : UU ℓ₁} {B : UU ℓ₂}
  → is-decidable A
  → is-decidable B
  → is-decidable (A → B)
→-is-decidable (inl a) (inl b) = inl λ x → b
→-is-decidable (inl a) (inr g) = inr λ h → g (h a)
→-is-decidable (inr f) (inl b) = inl (ex-falso ∘ f)
→-is-decidable (inr f) (inr g) = inl (ex-falso ∘ f)

Eqℕ-is-decidable : (m n : ℕ)
  → is-decidable (Eqℕ m n)
Eqℕ-is-decidable zero zero = 𝟙-is-decidable
Eqℕ-is-decidable zero (suc n) = 𝟘-is-decidable
Eqℕ-is-decidable (suc m) zero = 𝟘-is-decidable
Eqℕ-is-decidable (suc m) (suc n) = Eqℕ-is-decidable m n

has-decidable-eq : UU ℓ₁ → UU ℓ₁
has-decidable-eq A = (x y : A) → is-decidable (x ≡ y)

↔-is-decidable : {A : UU ℓ₁} {B : UU ℓ₂}
  → A ↔ B
  → is-decidable A ↔ is-decidable B
↔-is-decidable (f , g)
  = f ⊎ᶠ (g ~) , g ⊎ᶠ (f ~)
