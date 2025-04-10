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
