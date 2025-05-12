```
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
```
