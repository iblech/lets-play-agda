```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ComputationalContent.Blueprints.Drinkers where
```

# Drinkers

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
```

```
postulate
  oracle : (A : Set) → A ⊎ ¬ A
```

```
drinker : (f : ℕ → Bool) → Σ[ n ∈ ℕ ] (f n ≡ true → ((m : ℕ) → f m ≡ true))
-- Holify
drinker f with oracle (Σ[ m ∈ ℕ ] f m ≢ true)
... | left  (m , fm≢true) = (m    , λ fm≡true → ⊥-elim (fm≢true fm≡true))
... | right p             = (zero , λ _ → λ m → LEM⇒DNE oracle (f m ≡ true) λ fm≢true → p (m , fm≢true))
```
