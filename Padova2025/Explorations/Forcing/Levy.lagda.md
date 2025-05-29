```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Explorations.Forcing.Levy (X : Set) (x₀ : X) where
```

# Lévy collapse

```
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Termination.Gas using (Maybe; nothing; just; lookupMaybe)
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.More
```

In the module on [Cohen forcing](Padova2025.Explorations.Forcing.Cohen.html),
we have introduced the generic sequence `ℕ → X`. By adding one more close to the
definition of the [eventually modality](Padova2025.Explorations.Forcing.Cohen.html#∇)
of that module, we can obtain the *generic surjection* `ℕ ↠ X`. This construction
will work even in case that `X` is uncountable, and indeed this case is the main
situation where we might want to apply Lévy collapse: In the forcing extension,
the type `X` will become countable.

```
L : Set
L = List X
```

```
data ∇ (P : L → Set) : L → Set where
  now    : {xs : L} → P xs → ∇ P xs
  later₀ : {xs : L} → ((x : X) → ∇ P (xs ∷ʳ x)) → ∇ P xs
  later₁ : {xs : L} → (x : X) → ((ys : L) → x ∈ xs ++ ys → ∇ P (xs ++ ys)) → ∇ P xs
```

In contrast with the [definition for Cohen forcing](Padova2025.Explorations.Forcing.Cohen.html#∇),
there are now two ways how a finite approximation can evolve to a better approximation.
Using `later₀`, a finite list `xs` can grow by one element on the right to become more defined.
Using `later₁ x`, a finite list can grow by one or many elements on the right to become more
surjective, more specifically to contain `x` among its terms.

::: Todo :::
Expand.
:::
