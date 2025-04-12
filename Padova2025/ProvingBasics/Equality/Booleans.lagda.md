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

The converse direction is more involved. One way to structure the
argument is to first verify an auxiliary lemma.

```
γ : (f : Bool → Bool) → (a : Bool) → f false ≡ a → f a ≡ true → ConstantlyTrue f
-- Holify
γ f false p q false = q
γ f false p q true  with trans (sym p) q
... | ()
γ f true  p q false = p
γ f true  p q true  = q
```

```
part₂ : (f : Bool → Bool) → is-tautology₁' f ≡ true → ConstantlyTrue f
part₂ f = {--}γ f (f false) refl{--}
```

::: Aside :::
This way of structuring the argument is due to Martín Escardó, who has explored this topic
[in great detail](https://martinescardo.github.io/TypeTopology/Various.RootsOfBooleanFunctions.html).
:::
