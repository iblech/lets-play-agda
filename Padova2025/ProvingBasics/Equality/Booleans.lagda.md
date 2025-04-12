```
module Padova2025.ProvingBasics.Equality.Booleans where
```

# Results on Booleans

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Operators
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```


## Exercise: Double negation

```
not² : (x : Bool) → not (not x) ≡ x
-- Holify
not² false = refl
not² true  = refl
```


## Exercise: Commutativity of logical AND

```
&&-comm : (x y : Bool) → (x && y) ≡ (y && x)
-- Holify
&&-comm false false = refl
&&-comm false true  = refl
&&-comm true  false = refl
&&-comm true  true  = refl
```


## Tautologies

[Before](Padova2025.ProgrammingBasics.HigherOrder.html) we have
discussed a function `is-tautology₁ : (Bool → Bool) → Bool` with the
purpose of returning `true` if and only if the first argument is
constantly `true`. A straightforward implementation is the following:

```code
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = f false && f true
```

However, a more cryptic implementation is also possible.

```
is-tautology₁' : (Bool → Bool) → Bool
is-tautology₁' f = f (f false)
```

Let us verify that this alternatively works correctly. To this end,
we first formalize what it means for a function to be constantly
`true`:

```
ConstantlyTrue : (Bool → Bool) → Set
ConstantlyTrue f = (x : Bool) → f x ≡ true
```

In other words, an element of the type `ConstantlyTrue f` is a
function which maps every input `x : Bool` to a witness that `f x ≡ true`.
We are then ready to state and prove that `is-tautology₁' f` correctly
returns `true` if `f` is constantly true:

```
part₁ : (f : Bool → Bool) → ConstantlyTrue f → is-tautology₁' f ≡ true
-- Holify
part₁ f p = p (f false)
```

::: Todo :::
Converse direction.
:::

<!--
```
{-# BUILTIN EQUALITY _≡_ #-}
part₂ : (f : Bool → Bool) → is-tautology₁' f ≡ true → ConstantlyTrue f
part₂ f p false with f false in eq
... | false = trans (sym eq) p
... | true  = refl
part₂ f p true with f false in eq
... | false = absurd (trans (sym eq) p)
  where
  absurd : {A : Set} → false ≡ true → A
  absurd ()
... | true  = p
```
-->
