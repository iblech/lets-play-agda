```
module Padova2025.ProvingBasics.Termination.WellFounded.Examples where
```

# Examples

```
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Termination.WellFounded.Base
import Padova2025.ProvingBasics.Termination.WellFounded.Scheme as Scheme
```

## Digits, revisited

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Termination.Ordering
```

Reimplement the [`digits₄` function](Padova2025.ProvingBasics.Termination.WellFounded.Base.html#digits₄)
using the [general recursion scheme](Padova2025.ProvingBasics.Termination.WellFounded.Scheme.html) by following the sketched outline.

```
digits-step : (x : ℕ) → ((y : ℕ) → y <' x → ℕ) → ℕ
digits-step zero       f = {--}zero{--}
digits-step x@(succ _) f = {--}succ (f (half x) (<⇒<' (half-< _))){--}
```

```
digits-step-extensional
  : (x : ℕ) (u v : (y : ℕ) → y <' x → ℕ)
  → ((y : ℕ) (p : y <' x) → u y p ≡ v y p)
  → digits-step x u ≡ digits-step x v
-- Holify
digits-step-extensional zero       u v p = refl
digits-step-extensional x@(succ _) u v p = cong succ (p (half x) (<⇒<' (half-< _)))
```

```
module D = Scheme {ℕ} _<'_ {λ _ → ℕ} digits-step digits-step-extensional ℕ-wf
```

```
digits₄' : ℕ → ℕ
digits₄' = D.rec
```

```
digits₄'-eq : (x : ℕ) → digits₄' (succ x) ≡ succ (digits₄' (half (succ x)))
digits₄'-eq x = D.rec-eq (succ x)
```


## Modulo, revisited

```
open import Padova2025.ProvingBasics.EvenOdd
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Termination.Ordering
```

Reimplement the [`_%_` function](Padova2025.ProvingBasics.Termination.Gas.html#_%_)
using the [general recursion scheme](Padova2025.ProvingBasics.Termination.WellFounded.Scheme.html) by following the sketched outline.

```
%-step : (b : ℕ) → IsPositive b → (x : ℕ) → ((y : ℕ) → y <' x → ℕ) → ℕ
-- Holify
%-step b b>0 x f with ≤-<-connex b x
... | left  b≤x = f (x ∸ b) (<⇒<' (monus-< x b b>0 b≤x))
... | right x<b = x
```

```
%-step-extensional
  : (b : ℕ) → (b>0 : IsPositive b)
  → (x : ℕ) (u v : (y : ℕ) → y <' x → ℕ)
  → ((y : ℕ) (p : y <' x) → u y p ≡ v y p)
  → %-step b b>0 x u ≡ %-step b b>0 x v
%-step-extensional b b>0 x u v p with ≤-<-connex b x
... | left  b≤x = p (x ∸ b) (<⇒<' (monus-< x b b>0 b≤x))
... | right x<b = refl
```

```
module M (b : ℕ) (b>0 : IsPositive b) = Scheme {ℕ} _<'_ {λ _ → ℕ} (%-step b b>0) (%-step-extensional b b>0) ℕ-wf
```

```
_%'_ : ℕ → ℕ → ℕ
a %' zero   = a
a %' succ b = M.rec (succ b) (case-succ b) a
```

```code
%'-<₀ : (a b : ℕ) → (b>0 : IsPositive b) → a ≥ b → %-step b b>0 a (λ y y<a → M.rec b b>0 y) < b
%'-<₀ a (succ b) b>0 a≥b with ≤-<-connex (succ b) a
... | left  b<a = {!%'-<₀ (a ∸ succ b) (succ b) b>0!}
... | right a≤b = a≤b
```
