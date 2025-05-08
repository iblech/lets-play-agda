```
open import Padova2025.ProvingBasics.Termination.WellFounded.Base
open import Padova2025.ProvingBasics.Equality.Base
```

The purpose of this module is to provide, given a recursion rule
called `step` in the context of a well-founded relation, the resulting
recursive function `rec` together with a verification that it validates
the recursion rule.

```
module Padova2025.ProvingBasics.Termination.WellFounded.Scheme
  {X : Set}
  (_<_ : X → X → Set)
  {A : X → Set}
  (step : (x : X) → ((y : X) → y < x → A y) → A x)
  (step-extensional : (x : X) (u v : (y : X) → y < x → A y) → ((y : X) (p : y < x) → u y p ≡ v y p) → step x u ≡ step x v)
  (wf : (x : X) → Acc _<_ x)
  where
```

# A general recursion scheme

```
go : (x : X) → Acc _<_ x → A x
-- Holify
go x (acc f) = step x (λ y y<x → go y (f y<x))
```

```
rec : (x : X) → A x
rec x = go x (wf x)
```

```
go-extensional : (x : X) (p q : Acc _<_ x) → go x p ≡ go x q
-- Holify
go-extensional x (acc f) (acc g) = step-extensional
  x
  (λ y y<x → go y (f y<x))
  (λ y y<x → go y (g y<x))
  (λ y y<x → go-extensional y (f y<x) (g y<x))
```

::: Aside :::
Assuming [function extensionality](Padova2025.Cubical.Issues.FunctionExtensionality.html),
we can verify (without supposing `step-extensional`) that any two
values of type `Acc _<_ x` are equal and hence trivially conclude
`go-extensional` just with `cong (go x)`. Function extensionality is
not available in standard Agda, but (unless we introduce custom
postulates) it is also not refuted. Hence in practice, it should
always be possible to supply `step-extensional`, even if it is a
nuisance.
:::

```
rec-eq : (x : X) → rec x ≡ step x (λ y y<x → rec y)
-- Holify
rec-eq x with wf x
... | acc f = go-extensional x (acc f) (acc λ y<x → wf _)
```
