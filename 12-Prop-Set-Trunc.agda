module 12-Prop-Set-Trunc where

open import 11-Fundamental-Theorem public

is-prop : (A : UU ℓ₁) → UU ℓ₁
is-prop A = (x y : A) → is-contr (x ≡ y)

𝟙-is-prop : is-prop 𝟙
𝟙-is-prop ＊ ＊ = refl ＊ , λ{ (refl .＊) → refl (refl ＊)}

𝟘-is-prop : is-prop 𝟘
𝟘-is-prop ()

Prop : (ℓ : _) → UU (lsuc ℓ)
Prop ℓ = Σ[ X ∈ UU ℓ ] (is-prop X)

is-set : (A : UU ℓ₁) → UU ℓ₁
is-set A = (x y : A) → is-prop (x ≡ y)
