```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProgrammingBasics.HigherOrder where
```

# Higher-order functions

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Operators
```

::: Todo ::
Add introduction.
:::


## Exercise: Unary tautologies

Implement a function `is-tautology₁?` which checks whether a given input
function is constantly true.

For instance, for the function `f` defined by `f x = x`, the result of
`is-tautology₁ f` should be `false`.

```
is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = {--}f false && f true
-- There is also the following more cryptic solution:
-- is-tautology₁ f = f (f false){--}

-- Tests
-- EX: is-tautology₁ (λ x → x)     ≡ false
-- EX: is-tautology₁ (λ x → false) ≡ false
-- EX: is-tautology₁ not           ≡ false
-- EX: is-tautology₁ (λ x → true)  ≡ true
```

<!--
TODO: Exercises about...
- verifying that is-tautology₁ does what it should do
- verifying the clever solution "f (f false)"
-->


## Exercise: Binary tautologies

Implement a function ``is-tautology₂?`` which checks whether a given input
function of two arguments is constantly true.

For instance, for the function `f` defined by `f x y = true`, the result of
`is-tautology₂ f` should be `true`.

```
is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = {--}is-tautology₁ (f false) && is-tautology₁ (f true){--}

-- Tests
-- EX: is-tautology₂ _&&_            ≡ false
-- EX: is-tautology₂ _&&'_           ≡ false
-- EX: is-tautology₂ _||_            ≡ false
-- EX: is-tautology₂ (λ x y → x)     ≡ false
-- EX: is-tautology₂ (λ x y → y)     ≡ false
-- EX: is-tautology₂ (λ x y → not x) ≡ false
-- EX: is-tautology₂ (λ x y → not y) ≡ false
-- EX: is-tautology₂ (λ x y → true)  ≡ true
-- TODO: check all 2^4 cases
```


## Exercise: Types are first-class values

Most statically typed programming languages have a strict separation between
values (which then exist only at runtime) and types (which then exist only at
compiletime, and which are erased in the resulting machine code). In Agda,
types are values in their own right---indeed, they are values of the type
`Set`---and we can freely manipulate them.

For instance, define a function `Endo` which inputs a type `X` and outputs the
type `X → X` of functions from `X` to `X`:

```
Endo : Set → Set
Endo X = {--}X → X{--}

-- Tests
module _ where private
  open import Agda.Primitive
  data _≡_ {ℓ : Level} {X : Set ℓ} : X → X → Set ℓ where
    refl : {x : X} → x ≡ x

  test : (X : Set) → Endo X ≡ (X → X)
  test X = refl
```


## Exercise: Composition of functions

Implement the higher-order function which inputs two composable functions and
outputs their composition.

```
infixr 9 _∘_
_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
-- Holify
_∘_ g f = λ x → g (f x)

-- Tests
-- EX: not ∘ not ≡ λ x → not (not x)
```
