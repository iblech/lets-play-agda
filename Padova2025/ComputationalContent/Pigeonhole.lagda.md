```
{-# OPTIONS --cubical-compatible #-}
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

The purpose of this case study is to deduce the (constructively available)
finitary pigeonhole principle from the (constructively preposterous) infinitary
one, and compare this proof with a direct proof.

```
FinitaryPigeonholePrinciple : (ℕ → Bool) → Set
FinitaryPigeonholePrinciple α = ∃[ i ] ∃[ j ] i < j × α i ≡ α j
```

```
direct : (α : ℕ → Bool) → FinitaryPigeonholePrinciple α
direct α with α zero in eq₀ | α one in eq₁ | α two in eq₂
... | false | false | _     = {--}zero , one , s≤s z≤n       , trans eq₀ (sym eq₁){--}
... | false | true  | false = {--}zero , two , s≤s z≤n       , trans eq₀ (sym eq₂){--}
... | false | true  | true  = {--}one  , two , s≤s (s≤s z≤n) , trans eq₁ (sym eq₂){--}
... | true  | false | false = {--}one  , two , s≤s (s≤s z≤n) , trans eq₁ (sym eq₂){--}
... | true  | false | true  = {--}zero , two , s≤s z≤n       , trans eq₀ (sym eq₂){--}
... | true  | true  | _     = {--}zero , one , s≤s z≤n       , trans eq₀ (sym eq₁){--}
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

Run `C-c C-v theorem ?` to inspect the unrolled proof term. It
references `? three` and hence definitely does *not* coincide with the
straightforward direct proof which just inspects `? zero`, `? one` and
`? two` and looks for two equal values among these three values.

Hence the classical proof of the finitary pigeonhole principle, using
the infinitary pigeonhole principle as an auxiliary tool, indeed
contains a nontrivial algorithm.
