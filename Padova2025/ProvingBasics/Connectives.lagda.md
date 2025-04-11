```
module Padova2025.ProvingBasics.Connectives where
```

# Logical connectives 🚧

```
-- In Haskell, Either A B
infixr 1 _⊎_
data _⊎_ (A : Set) (B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
```
