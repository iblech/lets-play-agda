```
module Padova2025.Equality.Definition where

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x
```
