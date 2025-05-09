```
module Padova2025.ProvingBasics.Termination.BoveCapretta.Digits where
```

# Digits, revisited

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.ProvingBasics.Termination.WellFounded.Base
```

## Representing the function

```
data Def : ℕ → Set
f₀ : (n : ℕ) → Def n → ℕ

data Def where
  base : Def zero
  step : {x : ℕ} → Def (half (succ x)) → Def (succ x)

f₀ zero       base     = zero
f₀ x@(succ _) (step p) = succ (f₀ (half x) p)
```


## Verifying totality by well-founded induction

```
total : (x : ℕ) → Def x
total x = go x (ℕ-wf x)
  where
  go : (x : ℕ) (gas : Acc _<'_ x) → Def x
  go zero       gas     = {--}base{--}
  go x@(succ _) (acc f) = {--}step (go (half x) (f (<⇒<' (half-< _)))){--}
```

```
digits₅ : ℕ → ℕ
digits₅ x = f₀ x (total x)
```


## Verifying the defining equation

```
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```

```
Def-prop : {x : ℕ} (p q : Def x) → p ≡ q
-- Holify
Def-prop base base = refl
Def-prop (step p) (step q) = cong step (Def-prop p q)
```

```
f₀-extensional : (x : ℕ) (p q : Def x) → f₀ x p ≡ f₀ x q
-- Holify
f₀-extensional x p q = cong (f₀ x) (Def-prop p q)
```

```
digits₅-eq : (x : ℕ) → digits₅ (succ x) ≡ succ (digits₅ (half (succ x)))
-- Holify
digits₅-eq x = cong succ (f₀-extensional (half (succ x)) _ _)
```
