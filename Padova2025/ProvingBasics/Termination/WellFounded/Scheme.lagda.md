```
open import Padova2025.ProvingBasics.Termination.WellFounded.Base

module Padova2025.ProvingBasics.Termination.WellFounded.Scheme
  {X : Set}
  (_<_ : X → X → Set)
  {A : X → Set}
  (step : (x : X) → ((y : X) → y < x → A y) → A x)
  where
```

# A general recursion scheme

```
go : (x : X) → Acc _<_ x → A x
go x (acc f) = step x (λ y y<x → go y (f y<x))
```
