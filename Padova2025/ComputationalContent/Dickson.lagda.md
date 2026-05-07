```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ComputationalContent.Dickson where
```

# Case study: Dickson's lemma

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Termination.Ordering
import Padova2025.ComputationalContent.DoubleNegation
import Padova2025.ComputationalContent.Fictions.Minima
```

The purpose of this module is to give a constructive proof of (a baby
version of) Dickson's lemma, using a constructively preposterous
assertion as a central ingredient, namely the claim that every
function `ℕ → ℕ` has a minimum.

In its basic form, Dickson's lemma states that for every map `α : ℕ → ℕ`,
there is a number `i` such that `α i ≤ α (succ i)`.

The constructivization of the classical proof proceeds almost by magic:

```
Dickson : (ℕ → ℕ) → Set
Dickson α = Σ[ i ∈ ℕ ] α i ≤ α (succ i)
```

```
theorem : (α : ℕ → ℕ) → Dickson α
theorem α = escape do
  (i , p) ← minimum α
  q       ← p (succ i)
  return (i , q)
  where
  open Padova2025.ComputationalContent.DoubleNegation  (Dickson α)
  open Padova2025.ComputationalContent.Fictions.Minima (Dickson α)
-- Equivalently:
-- theorem α = escape (minimum f ⟫= λ (i , p) → p (succ i) ⟫= λ fi≤fsucci → return (i , fi≤fsucci))
--   where
--   open Padova2025.ComputationalContent.DoubleNegation  (Dickson α)
--   open Padova2025.ComputationalContent.Fictions.Minima (Dickson α)
```


## Arbitrarily good local minima

```
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProgrammingBasics.Lists
```

A `k`-th order approximative minimum of a map `α : ℕ → ℕ` is a number
`n` such that `α n ≤ α (i + n)` for all numbers `i < n`:

```
ApproximativeMinimum : (ℕ → ℕ) → ℕ → Set
ApproximativeMinimum α k = Σ[ n ∈ ℕ ] All (λ i → α n ≤ α (i + n)) (upTo k)
```

Every true minimum is also a `k`-th order approximative minimum, for every number `k`.
The following exercise demonstrates that the dynamical minimum
computed by the [`minimum` function](Padova2025.ComputationalContent.Fictions.Minima.html#minimum)
also gives rise to such approximative minima.

```
arbitrarily-good-approximative-minimum : (α : ℕ → ℕ) (k : ℕ) → ApproximativeMinimum α k
-- Holify
arbitrarily-good-approximative-minimum α k = escape do
  (n , p) ← minimum α
  ps      ← sequence (tabulate (upTo k) λ {i} _ → p (i + n))
  return (n , ps)
  where
  open Padova2025.ComputationalContent.DoubleNegation  (ApproximativeMinimum α k)
  open Padova2025.ComputationalContent.Fictions.Minima (ApproximativeMinimum α k)
```
