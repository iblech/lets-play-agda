```
module Padova2025.ProvingBasics.Equality.Reasoning.Core where

open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General

infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡˘⟨_⟩_ _≡⟨⟩_
infix  1 begin_

_≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_≡˘⟨_⟩_ : {A : Set} {y z : A} → (x : A) → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = trans (sym p) q

_≡⟨⟩_ : {A : Set} {y : A} → (x : A) → x ≡ y → x ≡ y
x ≡⟨⟩ q = q

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p
```
