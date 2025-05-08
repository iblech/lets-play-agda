```
module Padova2025.ProgrammingBasics.Naturals.Arithmetic where
```

# Arithmetic

```
open import Padova2025.ProgrammingBasics.Naturals.Base
```

Beyond the definition of the natural numbers, a canonical next step is to
define basic arithmetic. For instance, the doubling function can be defined by
pattern matching as follows.

```
twice : ℕ → ℕ
twice zero     = zero
twice (succ x) = succ (succ (twice x))
```

A more involved example is provided by addition:

```
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)
```

As in the section on [Operators](Padova2025.ProgrammingBasics.Operators.html),
the underscores in the name of the addition function allow us to use it as an
infix operator.

The right-hand side of the second clause in the definition is lifted straight
from the [Peano axioms](https://en.wikipedia.org/wiki/Peano_axioms). It is
mostly a matter of taste whether to do the case split on the first argument, as
done above, or instead on the second argument. One way to obtain this
definition if one is familiar with high school mathematical laws but not the
Peano axioms is as follows:

```
-- (intuitively, in blackboard mathematics)
-- succ a + b = (1+a) + b = 1 + (a+b) = succ (a + b)
```

As a sanity check, put some example computation in the hole below (for instance
`two + two`) and verify using `C-c C-v` that the result is what you would
expect:

```
example-computation : ℕ
example-computation = {--}two + two{--}
```


## Exercise: Halving

Define a function `half` which divides its input by two, rounding down if
required. For instance `half four` should reduce to `two` and `half three`
should reduce to `one`.

```
half : ℕ → ℕ
-- Holify
half zero            = zero
half (succ zero)     = zero
half (succ (succ n)) = succ (half n)

-- Tests
-- EX: half zero ≡ zero
-- EX: half (succ (succ (succ zero))) ≡ succ zero
-- EX: half (succ (succ (succ (succ zero)))) ≡ succ (succ zero)
-- EX: half (succ (succ (succ (succ (succ zero))))) ≡ succ (succ zero)
-- EX: half (succ (succ (succ (succ (succ (succ zero)))))) ≡ succ (succ (succ zero))
```

::: Aside :::
We could also write the type signature of `half` as follows:

```code
half : (x : ℕ) → ℕ
```

This style is especially useful in case we want the result type, in this case
`ℕ`, to depend on the input value `x`. This syntax is reminiscent of the
notation for the universal quantifier used in the beginning of the 20th
century: What we now write as "$\forall(x \in X).\ \ldots$" used to be written
as "$(x \in X)\ (\ldots)$", as in "$(x \in ℕ)\ (y \in ℕ)\ ((x+y)² = x² + 2xy + y²)$.
And indeed, a function associates to *every input* some output, so mimicking
the notation of the universal quantifier makes sense.
:::


## Exercise: Predecessor

Implement the predecessor function. For simplicity, let us agree that the
predecessor of `zero` is `zero` again (instead of introducing negative numbers
or error handling).

```
pred : ℕ → ℕ
-- Holify
pred zero     = zero
pred (succ x) = x

-- Tests
-- EX: pred zero ≡ zero
-- EX: pred four ≡ three
```

::: Aside :::
Again, we could also write the type signature as `pred : (x : ℕ) → ℕ`.
:::


## Exercise: Subtraction

Define (cut-off) subtraction. For instance `one ∸ one` and `one ∸ two` should
both result in `zero`.

```
infixl 6 _∸_
```

```
_∸_ : ℕ → ℕ → ℕ  -- enter `∸` as `\.-`
a      ∸ zero   = {--}a{--}
zero   ∸ succ b = {--}zero{--}
succ a ∸ succ b = {--}a ∸ b{--}

-- Tests
-- EX: (one  ∸ one)   ≡ zero
-- EX: (one  ∸ two)   ≡ zero
-- EX: (four ∸ zero)  ≡ four
-- EX: (four ∸ one)   ≡ three
-- EX: (four ∸ two)   ≡ two
-- EX: (four ∸ three) ≡ one
-- EX: (four ∸ four)  ≡ zero
```


## Exercise: Multiplication and exponentiation

Define multiplication and exponentiation.

```
infixl 7 _·_
```

```
_·_ : ℕ → ℕ → ℕ
zero   · b = {--}zero{--}
succ a · b = {--}b + (a · b){--}

-- Tests
-- EX: (two · three) ≡ succ (succ (succ (succ (succ (succ zero)))))
```


## Exercise: Squaring

Define squaring, without using the exponentiation operator introduced below.

```
infixr 8 _²
```

```
_² : ℕ → ℕ
_² x = {--}x · x{--}

-- Tests
-- EX: two ²   ≡ four
-- EX: three ² ≡ four + four + one
```

::: Aside :::
We could define squaring by reducing to exponentiation, i.e. defining `x ² = x ^ 2`.
This alternative definition would give the same results as the definition
envisioned here, and we will be able to state and prove this fact in Agda.
However, it is sometimes useful that `x ²` is the same as `x · x` *by
definition* instead of *by a nontrivial proof*. We will touch on this fine
point again [later](Padova2025.ProvingBasics.Equality.Base.html).
:::


## Exercise: Exponentiation

```
infixr 8 _^_
```

```
_^_ : ℕ → ℕ → ℕ
a ^ zero   = {--}one{--}
a ^ succ b = {--}a · (a ^ b){--}

-- Tests
-- EX: (two ^ three) ≡ succ (succ (succ (succ (succ (succ (succ (succ zero)))))))
```


## Exercise: Maximum

Define a function `max` which returns the maximum of two inputs.
For instance `max one four` should be `four`.

```
max : ℕ → ℕ → ℕ
-- Holify
max zero     b        = b
max (succ a) zero     = succ a
max (succ a) (succ b) = succ (max a b)

-- Tests
-- EX: max three four ≡ four
-- EX: max four  one  ≡ four
```
