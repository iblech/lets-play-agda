```
module Padova2025.ComputationalContent.Fictions.Drinkers (⊥ : Set) where
```

# Drinkers

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ComputationalContent.DoubleNegation (⊥)
```

```
drinker : (f : ℕ → Bool) → ¬ ¬ (Σ[ n ∈ ℕ ] (f n ≡ true → ((m : ℕ) → ¬ ¬ (f m ≡ true))))
-- Holify
drinker f = λ k → k (zero , (λ f0≡true m fm≢true → k (m , (λ fm≡true m' fm'≢true → fm≢true fm≡true))))
```
