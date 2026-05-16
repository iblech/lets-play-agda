```
{-# OPTIONS --cubical-compatible #-}

open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
import Padova2025.Recreational.Choice.Boxes.Base as Base

module Padova2025.Recreational.Choice.Boxes.Stage1
  (ℝ : Set) (n : ℕ)
  (open Base ℝ n)
  (p : Player) where
```

# Stage 1

We commit to inspect every other player's lane fully.

```
I : Set
I = Σ[ q ∈ Player ] q ≢ p × ℕ

their-box-indices : I → ℕ
their-box-indices (q , _ , m) = pack q m
```
