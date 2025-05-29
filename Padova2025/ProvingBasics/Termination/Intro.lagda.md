```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Termination.Intro where
```

# Intro

Let us implement a function which counts the binary digits of a number
(not counting trailing zeros). Using the
[`half`](Padova2025.ProgrammingBasics.Naturals.Arithmetic.html#half)
function, we could imagine the following definition.

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```

```code
digits : ℕ → ℕ
digits zero       = zero
digits x@(succ _) = succ (digits (half x))
```

Seems reasonable enough, for instance we have the following chain of reductions:

```code
digits five = succ (digits two) = succ (succ (digits one)) = succ (succ (succ zero))
```

However, Agda rejects this attempt with the comment "Termination
checking failed": In Agda, all functions are required to be total,
infinite loops are not allowed; but it is not obvious to Agda's
termination checker that the recursion eventually reaches the base
case `digits zero`. It does, as `half x` is strictly smaller than `x`
if `x` is positive, and we will [prove this
fact](Padova2025.ProvingBasics.Termination.Ordering.html#exercise-halving),
but neither this fact nor its relevance to the termination issue
is evident to the termination checker.

::: Aside :::
Most other programming languages, including Haskell which is in many
ways quite similar to Agda, are much more lenient with non-total
functions or functions which are total but not visibly so. Agda's
requirement that all functions need to be total is fundamental
to the [propositions as types](Padova2025.ProvingBasics.PropositionsAsTypes.html)
paradigm. If we would allow non-total functions, we could easily prove `⊥`:

```code
contradiction : ⊥
contradiction = contradiction
```
:::

There are the following ways for tackling this issue.

0. Employ a different algorithm which visibly terminates.
1. Promise to Agda that the recursion terminates, without supplying a proof.
2. Mark the function as non-terminating (which precludes its unfolding in proofs).
3. Use a simple but brittle kind of gas.
4. Use a more sophisticated kind of gas in the form of *accessibility witnesses*.
5. Supply a proof of termination.

Let us examine these options in turn.


## Employing a different algorithm

This option is in general untenable. For the specific case here, we
could first compute the binary representation of the input number and
then count the number of bits:

```
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.VerifiedAlgorithms.Binary

digits₀ : ℕ → ℕ
digits₀ n = length (encode n)
```

This definition works as expected.


## Promising termination

Promising termination is a quick way to get the issue out of the way,
perhaps to focus on other, more interesting features of a
formalization project. This option is also unsatisfactory, and
unavailable when using Agda's safe mode (which can be switched on by
putting `{-# OPTIONS --safe #-}` at the beginning of an Agda file).

```
{-# TERMINATING #-}
digits₁ : ℕ → ℕ
digits₁ zero       = zero
digits₁ x@(succ _) = succ (digits₁ (half x))
```



## Marking as non-terminating

A marginally safer variant of `{-# TERMINATING #-}` is to mark the
definition as non-terminating. We can then still run this function
using `C-c C-v`, but the definition will never be unfolded during type
checking.

```
{-# NON_TERMINATING #-}
digits₂ : ℕ → ℕ
digits₂ zero       = zero
digits₂ x@(succ _) = succ (digits₂ (half x))

-- The following hole cannot be filled.
-- In particular, `refl` will not work.
-- open import Padova2025.ProvingBasics.Equality.Base
-- _ : digits₂ zero ≡ zero
-- _ = ?
```

Using `{-# NON_TERMINATING #-}` still renders the system inconsistent,
just as using `{-# TERMINATING #-}` does---we can "prove" `⊥` as follows.

```
open import Padova2025.ProvingBasics.Negation

{-# NON_TERMINATING #-}
loop : ⊥  -- 😱
loop = loop
```


## Using gas and proving termination

Options 3, 4 and 5 are discussed in the following modules.

```
-- Option 3
open import Padova2025.ProvingBasics.Termination.Gas

-- Option 4
open import Padova2025.ProvingBasics.Termination.WellFounded

-- Option 5
open import Padova2025.ProvingBasics.Termination.BoveCapretta
```

But first, we have a look at the standard ordering relation on the
naturals.

```
open import Padova2025.ProvingBasics.Termination.Ordering
```
