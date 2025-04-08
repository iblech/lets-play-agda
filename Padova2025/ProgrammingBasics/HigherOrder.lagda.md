```
module Padova2025.ProgrammingBasics.HigherOrder where
```

# Higher-order functions

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Operators
```

::: Todo ::
Introduction.
:::


## Exercise: Unary tautologies

Implement a function `is-tautology₁?` which checks whether a given input
function is constantly true.

```
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = {--}f false && f true{--}

-- Tests
-- EX: is-tautology₁ (λ x → x)    ≡ false
-- EX: is-tautology₁ (λ x → true) ≡ true
-- EX: is-tautology₁ not          ≡ false
```

For instance, for the function `f` defined by `f x = x`, the result of
`is-tautology₁ f` should be `false`.


## Exercise: Binary tautologies

Implement a function ``is-tautology₂?`` which checks whether a given input
function of two arguments is constantly true.

```
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = {--}is-tautology₁ (f false) && is-tautology₁ (f true){--}

-- Tests
-- EX: is-tautology₂ _&&_            ≡ false
-- EX: is-tautology₂ _&&'_           ≡ false
-- EX: is-tautology₂ _||_            ≡ false
-- EX: is-tautology₂ (λ x y → x)     ≡ false
-- EX: is-tautology₂ (λ x y → not x) ≡ false
-- EX: is-tautology₂ (λ x y → true)  ≡ true
```

For instance, for the function `f` defined by `f x y = true`, the result of
`is-tautology₂ f` should be `true`.
