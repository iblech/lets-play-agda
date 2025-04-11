```
module Padova2025.ProvingBasics.Equality.Vectors where
```

# Results on vectors

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Vectors
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```

## Take and drop

```
take-drop
  : {A : Set} {n : ℕ} (k : ℕ) (xs : Vector A (k + n))
  → takeV k xs ++V dropV k xs ≡ xs
-- Holify
take-drop zero     xs       = refl
take-drop (succ k) (x ∷ xs) = cong (x ∷_) (take-drop k xs)
```


## Associativity

Determine where the difficulty is in stating that `_++V_` is associative.

::: More :::
Let `xs : Vector A n`, `ys : Vector A m` and `zs : Vector A o`.

Then `(xs ++V ys) ++V zs` is of type `Vector A ((n + m) + o`, whereas `xs ++V (ys ++V zs)`
is of type `Vector A (n + (m + o))`.

These two types are equal, but not by definition. Hence the expression "`(xs
++V ys) ++V zs ≡ xs ++V (ys ++V zs)`" is ill-typed.
:::
