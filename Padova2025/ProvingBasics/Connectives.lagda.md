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


## Exercise: Even or odd

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.DependentFunctions
open import Padova2025.ProvingBasics.EvenOdd
```

```
even-or-odd : (x : ℕ) → Even x ⊎ Odd x
even-or-odd zero            = left base-even
even-or-odd (succ zero)     = right base-odd
even-or-odd (succ (succ x)) with even-or-odd x
... | left  p = left  (step-even p)
... | right p = right (step-odd p)
```
