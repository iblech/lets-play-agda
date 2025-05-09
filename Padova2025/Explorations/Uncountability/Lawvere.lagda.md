```
module Padova2025.Explorations.Uncountability.Lawvere
  {A X : Set} (f : A → (A → X)) (g : X → X) where
```

# Lawvere's fixed point theorem

```
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Existential
```

```
canary : A → X
-- Holify
canary a = g (f a a)
```

```
fix : ∃[ a ] canary ≗ f a → ∃[ x ] g x ≡ x
-- Holify
fix (a , p) = f a a , p a
```

```
fix₀ : ((h : A → X) → ∃[ a ] h ≗ f a) → ∃[ x ] g x ≡ x
-- Holify
fix₀ split-surjectivity = fix (split-surjectivity canary)
```
