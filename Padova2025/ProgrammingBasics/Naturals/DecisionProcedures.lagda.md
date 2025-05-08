```
module Padova2025.ProgrammingBasics.Naturals.DecisionProcedures where
```

# Decision procedures

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Booleans
```

This file contains a couple of decision procedures---functions which have the
task of answering certain yes/no questions, such as: *Is the given input number
zero? Is it even?*

We will later improve on the definitions suggested here. The issue is that the
functions of this file do not actually return a *witness* ("yes, the number is
zero, here is why" or "no, the number is not zero, here is why") but instead
merely a non-informative Boolean value (`true` or `false`).


## Exercise: Equality checking

Define a function `eq?` which determines whether its two
input numbers are equal. For instance, `eq? three three` should reduce to
`true` while `eq? three four` should reduce to `false`.

```
eq? : ℕ → ℕ → Bool
-- Holify
eq? zero     zero     = true
eq? zero     (succ b) = false
eq? (succ a) zero     = false
eq? (succ a) (succ b) = eq? a b

-- Tests
-- EX: eq? zero  zero  ≡ true
-- EX: eq? three three ≡ true
-- EX: eq? three four  ≡ false
-- EX: eq? two   four  ≡ false
```


## Exercise: Inequality checking

Define a function `≤?` which determines whether its first argument is less than
or equal to its second. For instance, `≤? two four` should reduce to `true`
while `≤? four two` should reduce to `false`.

```
≤? : ℕ → ℕ → Bool
-- Holify
≤? zero     b        = true
≤? (succ a) zero     = false
≤? (succ a) (succ b) = ≤? a b

-- Tests
-- EX: ≤? two  four ≡ true
-- EX: ≤? four two  ≡ false
```

Building on `≤?`, we can implement a decision procedure for the strict
less-than relation:

```
<? : ℕ → ℕ → Bool
<? a b = ≤? (succ a) b
```


## Exercise: Even and odd numbers

Define a function `even?` which determines whether its input is even.

For instance, `even? zero` and `even? two` should both reduce to `true`, while
`even? three` should evaluate to `false`.

```
even? : ℕ → Bool
-- Holify
even? zero            = true
even? (succ zero)     = false
even? (succ (succ a)) = even? a
-- Alternatively, the following definition works:
-- even? zero     = true
-- even? (succ a) = not (even? a)

-- Tests
-- EX: even? zero  ≡ true
-- EX: even? two   ≡ true
-- EX: even? four  ≡ true
-- EX: even? one   ≡ false
-- EX: even? three ≡ false
```

Define a function `odd?` which determines whether its input is odd.
You may use the `even?` function from before.

```
odd? : ℕ → Bool
-- Holify
odd? n = not (even? n)

-- Alternatively:
-- odd? zero            = false
-- odd? (succ zero)     = true
-- odd? (succ (succ a)) = odd? a

-- Or also:
-- odd? zero            = false
-- odd? (succ a)        = not (odd? a)

-- Tests
-- EX: odd? zero  ≡ false
-- EX: odd? two   ≡ false
-- EX: odd? four  ≡ false
-- EX: odd? one   ≡ true
-- EX: odd? three ≡ true
```

