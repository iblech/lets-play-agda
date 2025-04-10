```
module Padova2025.ProvingBasics.EvenOdd where
```

# Predicates on natural numbers

From the five assertions discussed [in the introduction to this
chapter](Padova2025.ProvingBasics.html), we will elevate the first two to
definitions.

```
open import Padova2025.ProgrammingBasics.Naturals.Base

data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))
```


## Exercise: Sanity checks

As basic sanity checks, let us prove that `zero` and `two` are both even.

```
zero-even : Even zero
zero-even = {--}base-even{--}

two-even : Even two
two-even = {--}step-even base-even{--}
```


## Exercise: Sum of even numbers

Verify that the sum of even numbers is even.

```
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```

```
sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
-- Holify
sum-even base-even     q = q
sum-even (step-even p) q = step-even (sum-even p q)
```


## Exercise: Successors of even numbers

Verify that the successor of an even number is odd. To this end, we define the
notion of odd numbers as follows.

```
data Odd : ℕ → Set where
  base-odd : Odd one
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))
```

```
succ-even : {a : ℕ} → Even a → Odd (succ a)
-- Holify
succ-even base-even     = base-odd
succ-even (step-even p) = step-odd (succ-even p)
```


## Exercise: Being zero

Soon we will discuss equality in general; as a warm-up, we want to set up a
family `IsZero n` of dependent types in such a way that their elements can be
regarded as witnesses for `n` being zero. In other words:

1. The type `IsZero zero` should be inhabited.
2. For all nonzero numbers `n`, the type `IsZero n` should be empty.

Think about how we can formalize this in Agda, then compare with the reference
solution:

::: More :::
```
data IsZero : ℕ → Set where
  case-zero : IsZero zero
```
:::

With this definition in place, we can state and prove that the sum of two
numbers, both of which are zero, is zero again. First think about how we could
formalize this claim, then have a look and fill in the hole.

::: More :::
```
sum-zero : (x y : ℕ) → IsZero x → IsZero y → IsZero (x + y)
-- Holify
sum-zero zero zero case-zero case-zero = case-zero
```

::: Hint :::
First introduce four variables to the left of the `=` sign: `x`, `y`, `p` (a
witness for `x` being zero), and `q` (a witness for `y` being zero). Then do
case splits. You will observe that Agda recognizes that the successor cases
cannot occur.
:::
:::


## Exercise: Being positive

Similar to the types `IsZero n` of the previous exercise, let us now introduce
types `IsPositive n`. The type `IsPositive zero` should be empty---there should
not be a witness of the false claim that `zero` is positive---and all the other
types `IsPositive n` should be inhabited.

Think about how this could be formalized in Agda, then compare with the
reference solution:

::: More :::
```
data IsPositive : ℕ → Set where
  case-succ : (n : ℕ) → IsPositive (succ n)
```
:::

Now think about how the observation "the sum of two numbers, the first one on
which is positive, is positive" can be formalized in Agda; then compare with
the reference solution; then fill in the hole.

::: More :::
```
sum-positive : (x y : ℕ) → IsPositive x → IsPositive (x + y)
-- Holify
sum-positive x y (case-succ n) = case-succ (n + y)

-- Alternatively:
-- sum-positive (succ x) y p = case-succ (x + y)
```
:::
