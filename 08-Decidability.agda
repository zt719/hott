module 08-Decidability where

open import 07-Curry-Howard public

is-decidable : {i : Level}
  → UU i → UU i
is-decidable A = A ∔ ¬ A

𝟙-is-decidable : is-decidable 𝟏
𝟙-is-decidable = inl ＊

Φ-is-decidable : is-decidable Φ
Φ-is-decidable = inr (id Φ)

∔-is-decidable : {i j : Level} {A : UU i} {B : UU j}
  → (x : is-decidable A) (y : is-decidable B) → is-decidable (A ∔ B)
∔-is-decidable (inl a) (inl b) = inl (inl a)
∔-is-decidable (inl a) (inr g) = inl (inl a)
∔-is-decidable (inr f) (inl b) = inl (inr b)
∔-is-decidable (inr f) (inr g) = inr [ f , g ]

×-is-decidable : {i j : Level} {A : UU i} {B : UU j}
  → (x : is-decidable A) (y : is-decidable B) → is-decidable (A × B)
×-is-decidable (inl a) (inl b) = inl (a , b)
×-is-decidable (inl a) (inr g) = inr (g ∘ pr₂)
×-is-decidable (inr f) (inl b) = inr (f ∘ pr₁)
×-is-decidable (inr f) (inr g) = inr (f ∘ pr₁)

→-is-decidable : {i j : Level} {A : UU i} {B : UU j}
  → (x : is-decidable A) (y : is-decidable B) → is-decidable (A → B)
→-is-decidable (inl a) (inl b) = inl λ x → b
→-is-decidable (inl a) (inr g) = inr λ h → g (h a)
→-is-decidable (inr f) (inl b) = inl (ex-falso ∘ f)
→-is-decidable (inr f) (inr g) = inl (ex-falso ∘ f)

Eqℕ-is-decidable :
  (m n : ℕ) → is-decidable (Eqℕ m n)
Eqℕ-is-decidable 0ℕ 0ℕ = inl ＊
Eqℕ-is-decidable 0ℕ (succℕ n) = inr (id Φ)
Eqℕ-is-decidable (succℕ m) 0ℕ = inr (id Φ)
Eqℕ-is-decidable (succℕ m) (succℕ n) = Eqℕ-is-decidable m n

has-decidable-eq : {i : Level}
  → (A : UU i) → UU i
has-decidable-eq A = (x y : A) → is-decidable (x ≡ y)

