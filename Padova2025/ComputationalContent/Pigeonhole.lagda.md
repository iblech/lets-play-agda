```
module Padova2025.ComputationalContent.Pigeonhole where
```

# Case study: Pigenhole principle

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Termination.Ordering
import Padova2025.ComputationalContent.DoubleNegation
import Padova2025.ComputationalContent.Fictions.InfinitelyMany
```

```
FinitaryPigeonholePrinciple : (ℕ → Bool) → Set
FinitaryPigeonholePrinciple α = ∃[ i ] ∃[ j ] i < j × α i ≡ α j
```

```
theorem : (α : ℕ → Bool) → FinitaryPigeonholePrinciple α
theorem α = escape (infinitary-pigeonhole-principle α ⟫= λ { (left p) → go p; (right p) → go p })
  where
  open Padova2025.ComputationalContent.DoubleNegation          (FinitaryPigeonholePrinciple α)
  open Padova2025.ComputationalContent.Fictions.InfinitelyMany (FinitaryPigeonholePrinciple α)

  go : {x : Bool} → Infinitely α (x ≡_) → ¬ ¬ FinitaryPigeonholePrinciple α
  go p = 
    {--}p zero     ⟫= λ (i , 0≤i , i-good) →
    p (succ i) ⟫= λ (j , i<j , j-good) →
    return (i , j , i<j , trans (sym i-good) j-good){--}
```
