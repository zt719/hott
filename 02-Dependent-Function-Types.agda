{-# OPTIONS --without-K --safe #-}

module 02-Dependent-Function-Types where

open import Agda.Primitive
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to 𝓤)
  
private variable 𝓲 𝓳 𝓴 : Level

Π : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π A B = (x : A) → B x
syntax Π A (λ x → b) = Π[ x ∶ A ] b

Π2 : (A : 𝓤 𝓲) (B : A → A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π2 A B = (x₁ x₂ : A) → B x₁ x₂
syntax Π2 A (λ x₁ x₂ → b) = Π[ x₁ x₂ ∶ A ] b

Π3 : (A : 𝓤 𝓲) (B : A → A → A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π3 A B = (x₁ x₂ x₃ : A) → B x₁ x₂ x₃
syntax Π3 A (λ x₁ x₂ x₃ → b) = Π[ x₁ x₂ x₃ ∶ A ] b

Π4 : (A : 𝓤 𝓲) (B : A → A → A → A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π4 A B = (x₁ x₂ x₃ x₄ : A) → B x₁ x₂ x₃ x₄
syntax Π4 A (λ x₁ x₂ x₃ x₄ → b) = Π[ x₁ x₂ x₃ x₄ ∶ A ] b

Π5 : (A : 𝓤 𝓲) (B : A → A → A → A → A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π5 A B = (x₁ x₂ x₃ x₄ x₅ : A) → B x₁ x₂ x₃ x₄ x₅
syntax Π5 A (λ x₁ x₂ x₃ x₄ x₅ → b) = Π[ x₁ x₂ x₃ x₄ x₅ ∶ A ] b

Π' : (A : 𝓤 𝓲) (B : A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π' A B = {x : A} → B x
syntax Π' A (λ x → b) = Π'[ x ∶ A ] b

Π2' : (A : 𝓤 𝓲) (B : A → A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π2' A B = {x₁ x₂ : A} → B x₁ x₂
syntax Π2' A (λ x₁ x₂ → b) = Π'[ x₁ x₂ ∶ A ] b

Π3' : (A : 𝓤 𝓲) (B : A → A → A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π3' A B = {x₁ x₂ x₃ : A} → B x₁ x₂ x₃
syntax Π3' A (λ x₁ x₂ x₃ → b) = Π'[ x₁ x₂ x₃ ∶ A ] b

Π4' : (A : 𝓤 𝓲) (B : A → A → A → A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π4' A B = {x₁ x₂ x₃ x₄ : A} → B x₁ x₂ x₃ x₄
syntax Π4' A (λ x₁ x₂ x₃ x₄ → b) = Π'[ x₁ x₂ x₃ x₄ ∶ A ] b

Π5' : (A : 𝓤 𝓲) (B : A → A → A → A → A → 𝓤 𝓳) → 𝓤 (𝓲 ⊔ 𝓳)
Π5' A B = {x₁ x₂ x₃ x₄ x₅ : A} → B x₁ x₂ x₃ x₄ x₅
syntax Π5' A (λ x₁ x₂ x₃ x₄ x₅ → b) = Π'[ x₁ x₂ x₃ x₄ x₅ ∶ A ] b

-- Ordinary Function Types
_⇒_ : 𝓤 𝓲 → 𝓤 𝓳 → 𝓤 (𝓲 ⊔ 𝓳)
A ⇒ B = Π[ x ∶ A ] B
infixr  0 _⇒_

id : (A : 𝓤 𝓲)
  → A ⇒ A
id A x = x

comp : {A : 𝓤 𝓲} {B : 𝓤 𝓳} {C : 𝓤 𝓴}
  → (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)
comp = λ g f x → g (f x)

_∘_ = comp
infixr 9 _∘_

const : {A : 𝓤 𝓲} {B : 𝓤 𝓳}
  → B ⇒ A ⇒ B
const y = λ _ → y

swap : {A : 𝓤 𝓲} {B : 𝓤 𝓳} {C : A → B → 𝓤 𝓴}
  → Π[ x ∶ A ] Π[ y ∶ B ] C x y
  ⇒ Π[ y ∶ B ] Π[ x ∶ A ] C x y
swap f x y = f y x

σ = swap
