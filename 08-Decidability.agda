module 08-Decidability where

open import 07-Curry-Howard public

is-decidable : UU l₁ → UU l₁
is-decidable A = A ⊎ ¬ A

𝟏-is-decidable : is-decidable 𝟏
𝟏-is-decidable = inl ＊

Φ-is-decidable : is-decidable Φ
Φ-is-decidable = inr id

⊎-is-decidable : {A : UU l₁} {B : UU l₂}
  → is-decidable A
  → is-decidable B
  → is-decidable (A ⊎ B)
⊎-is-decidable (inl a) (inl b) = inl (inl a)
⊎-is-decidable (inl a) (inr g) = inl (inl a)
⊎-is-decidable (inr f) (inl b) = inl (inr b)
⊎-is-decidable (inr f) (inr g) = inr [ f , g ]

×-is-decidable : {A : UU l₁} {B : UU l₂}
  → is-decidable A
  → is-decidable B
  → is-decidable (A × B)
×-is-decidable (inl a) (inl b) = inl (a , b)
×-is-decidable (inl a) (inr g) = inr (g ∘ pr₂)
×-is-decidable (inr f) (inl b) = inr (f ∘ pr₁)
×-is-decidable (inr f) (inr g) = inr (f ∘ pr₁)

→-is-decidable : {A : UU l₁} {B : UU l₂}
  → is-decidable A
  → is-decidable B
  → is-decidable (A → B)
→-is-decidable (inl a) (inl b) = inl λ x → b
→-is-decidable (inl a) (inr g) = inr λ h → g (h a)
→-is-decidable (inr f) (inl b) = inl (ex-falso ∘ f)
→-is-decidable (inr f) (inr g) = inl (ex-falso ∘ f)

Eqℕ-is-decidable : (m n : ℕ)
  → is-decidable (Eqℕ m n)
Eqℕ-is-decidable 0ℕ 0ℕ = 𝟏-is-decidable
Eqℕ-is-decidable 0ℕ (succℕ n) = Φ-is-decidable
Eqℕ-is-decidable (succℕ m) 0ℕ = Φ-is-decidable
Eqℕ-is-decidable (succℕ m) (succℕ n) = Eqℕ-is-decidable m n

has-decidable-eq : UU l₁ → UU l₁
has-decidable-eq A = (x y : A) → is-decidable (x ≡ y)

↔-is-decidable : {A : UU l₁} {B : UU l₂}
  → A ↔ B
  → is-decidable A ↔ is-decidable B
↔-is-decidable (f , g)
  = (f ⊎ᶠ (g ~)) , (g ⊎ᶠ (f ~))
