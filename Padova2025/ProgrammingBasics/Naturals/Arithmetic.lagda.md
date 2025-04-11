```
module Padova2025.ProgrammingBasics.Naturals.Arithmetic where
```

# Arithmetic

```
open import Padova2025.ProgrammingBasics.Naturals.Base
```

Beyond the definition of the natural numbers, a canonical next step is to
define basic arithmetic. For instance, addition can be defined by pattern
matching as follows.

```
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)
```

As in the section on [Operators](Padova2025.ProgrammingBasics.Operators.html),
the underscores in the name of the addition function allow us to use it as an
infix operator.

The right hand side of the second clause in the definition is lifted straight
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
```


## Exercise: Subtraction

Define (cut-off) subtraction. For instance `one - one` and `one - two` should
both result in `zero`.

```
infixl 6 _-_
```

```
_-_ : ℕ → ℕ → ℕ
zero   - b      = {--}zero{--}
succ a - zero   = {--}succ a{--}
succ a - succ b = {--}a - b{--}

-- Tests
-- EX: (one - one)    ≡ zero
-- EX: (one - two)    ≡ zero
-- EX: (four - zero)  ≡ four
-- EX: (four - one)   ≡ three
-- EX: (four - two)   ≡ two
-- EX: (four - three) ≡ one
-- EX: (four - four)  ≡ zero
```


## Exercise: Multiplication and exponentiation

Define multiplication and exponentiation.

```
infixl 7 _*_
infixr 8 _^_
```

```
_*_ : ℕ → ℕ → ℕ
zero   * b = {--}zero{--}
succ a * b = {--}b + (a * b){--}

-- Tests
-- EX: (two * three) ≡ succ (succ (succ (succ (succ (succ zero)))))
```

```
_^_ : ℕ → ℕ → ℕ
a ^ zero   = {--}one{--}
a ^ succ b = {--}a * (a ^ b){--}

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


