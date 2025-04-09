```
module Padova2025.Equality.Definition where

open import Agda.Primitive

data _≡_ {ℓ : Level} {X : Set ℓ} : X → X → Set ℓ where
  refl : {x : X} → x ≡ x
```
