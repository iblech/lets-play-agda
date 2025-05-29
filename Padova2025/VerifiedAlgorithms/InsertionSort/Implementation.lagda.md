```
{-# OPTIONS --cubical-compatible #-}
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Connectives.Disjunction

module Padova2025.VerifiedAlgorithms.InsertionSort.Implementation
  (A : Set) (_≤_ : A → A → Set) (cmp? : (x y : A) → x ≤ y ⊎ y ≤ x) where
```

# Implementation

::: Todo :::
Explanation
:::

Contract: "insert x ys" is ascendingly ordered, if "ys" is ascendingly ordered.

```
insert : A → List A → List A
-- Holify
insert x []       = x ∷ []
insert x (y ∷ ys) with cmp? x y
... | left  x≤y = x ∷ (y ∷ ys)
... | right y≤x = y ∷ insert x ys
```

```
sort : List A → List A
-- Holify
sort []       = []
sort (x ∷ xs) = insert x (sort xs)
```
