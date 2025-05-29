```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProgrammingBasics.Naturals.Base where
```

# Definition

In the previous chapter, we have defined the finite type of Booleans. Agda also
supports infinite types. The natural numbers are the primordial example, and we
will explore them now.
The type of natural numbers is brought into existence with the following three
lines of Agda code.

```
data ℕ : Set where  -- enter "ℕ" by "\bN"
  zero : ℕ
  succ : ℕ → ℕ      -- short for "successor"
```

The `succ` constructor outputs, for each input, a new freshly-minted value
of the type `ℕ`. Hence the type `ℕ` contains the following distinct
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

five : ℕ
five = succ four
```

::: Aside :::
Writing natural numbers in unary is a pain. By adding `{-# BUILTIN NATURAL ℕ #-}`
on a line of its own, we can ask Agda to enable suitable syntactic sugar.
From then on, we can write decimal expressions like `42` which Agda will transparently
desugar to appropriate `succ` calls: `succ (succ (... (zero)))`.
:::
