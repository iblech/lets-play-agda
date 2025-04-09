```
module Padova2025.ProgrammingBasics.Naturals where
```

# Natural numbers

```
open import Padova2025.ProgrammingBasics.Booleans
```

In the previous chapter, we have defined the finite type of Booleans. Agda also
supports infinite types. The natural numbers are the primordial example:

```
data ℕ : Set where  -- enter "ℕ" by "\bN"
  zero : ℕ
  succ : ℕ → ℕ      -- short for "successor"
```

The `succ` constructor will output, for each input, a new freshly-minted value
of the type `ℕ`. Hence the type `ℕ` will contain the following distinct
elements:

```
-- zero
-- succ zero
-- succ (succ zero)
-- succ (succ (succ zero))
-- ...
```

We can define abbreviations for often-occuring numbers:

```
one : ℕ
one = succ zero

two : ℕ
two = succ one

three : ℕ
three = succ two

four : ℕ
four = succ three
```

::: Aside :::
Writing natural numbers in unary is a pain. By adding `{-# BUILTIN NATURAL ℕ #-}`
on a line of its own, we can ask Agda to enable suitable syntactic sugar.
From then on, we can write expressions like `42` which Agda will transparently
desugar to appropriate `succ` calls: `succ (succ (... (zero)))`.
:::


## Addition

```
_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ a + b = succ (a + b)
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
