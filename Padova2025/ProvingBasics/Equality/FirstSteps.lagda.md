```
module Padova2025.ProvingBasics.Equality.FirstSteps where
```

# First steps with equality

```
open import Padova2025.ProvingBasics.Equality.Base
```


## Example: Our first identities

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```

With the definition of equality at hand, we can state and prove that `zero`
equals `zero`:

```
zero-equals-zero : zero ≡ zero
zero-equals-zero = refl
```

In exactly the same fashion, we can state and prove that `two + two` equals
`four`:

```
grande-teorema : two + two ≡ four
-- fully parenthesized as follows: grande-teorema : ((two + two) ≡ four)
grande-teorema = refl
```

We can use `refl` in exactly those situations, where the two sides of the
alleged identity are *manifestly equal*, i.e. equal in a way which just
requires unfolding all definitions and simplifying by computation, but no
actual insights, to become convinced of the equality.

For instance, as `zero + b` equals `b` [by
definition](Padova2025.ProgrammingBasics.Naturals.Arithmetic.html#_+_), `refl` can
be used in the following proof:

```
trivial : (b : ℕ) → zero + b ≡ b
-- fully parenthesized: lemma : (b : ℕ) → ((zero + b) ≡ b)
trivial b = refl
```

This piece of code can (as all pieces of Agda code!) be both read in a logical
and in a computational sense:

> (logical reading) \
> "lemma" is the result that for every number `b`, `zero + b` equals `b`.
>
> (computational reading) \
> "lemma" is a function which reads as input a number `b`, and outputs a
> witness that `zero + b` equals `b`.

It is also true that `a + zero` equals `a`. However, this identity does not
hold *by definition*; instead it requires a [nontrivial (inductive)
argument](Padova2025.ProvingBasics.Equality.NaturalNumbers.html#+-zero).
For this reason, Agda rejects `refl` in the following attempt:

```code
nontrivial : (a : ℕ) → a + zero ≡ a
nontrivial a = refl
-- ERROR:
-- a + zero != a of type ℕ
-- when checking that the expression refl has type a + zero ≡ a
```


## Example: One not zero

It is not the case that `one` equals `zero`. And indeed, the hole in the
following piece of Agda code cannot be filled:

```code
outrageous : one ≡ zero
outrageous = ?
```

It is instructive to understand why this is the case. At the end of the day,
for constructing an inhabitant of the type `one ≡ zero`, we will need to use a
constructor of this type. But the only constructor is `refl`. This constructor
only provides us with elements of types of the for `x ≡ x`, where the two sides
are literally the same. But `succ zero` is (by definition) a freshly-minted new
natural number, distint from `zero`.

The only way to fill in this hole would be to change the definition of `≡`. For
instance, we could add a constructor `bailout`:

```
data _≡'_ {X : Set} : X → X → Set where
  refl    : {x   : X} → x ≡' x
  bailout : {x y : X} → x ≡' y

outrageous' : one ≡' zero
outrageous' = bailout
```


## Exercise: Predecessor of successor

Prove that the predecessor of a successor of a number is the original number
again.

```
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ a = {--}refl{--}
```


## Unit tests

If a definition is not used in the remainder of a development, Agda supports
giving it the reusable dummy name "`_`". This feature is used in the Agda
community to document expected results as rigorously verified unit tests,
instead of merely putting examples in comments.

```
_ : twice two ≡ four
_ = refl
```

