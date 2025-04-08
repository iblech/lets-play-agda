```
module Padova2025.ProgrammingBasics.Booleans where
```

# Booleans

The following three lines of code introduce a new datatype, `Bool`. This type contains
precisely two values, `false` and `true`:

```
data Bool : Set where
  false : Bool
  true  : Bool
```

In Agda, every term is of a certain type. The type of a term is indicated by a
colon. Thus the terms `false` and `true` are of type `Bool`, and `Bool` itself
is of type `Set`. We picture types as containers of values, similar to sets in
blackboard mathematics. The type `Set` is built into Agda and does not need to
(and cannot) be manually defined. It contains all the so-called small
datatypes.

::: Aside :::
In standard set theory, having a "set of all sets" is an incoherent idea,
enabling [Russell's paradox](https://en.wikipedia.org/wiki/Russell%27s_paradox).

In a similar vein, in type theory we cannot have a "type of all types", else
Girard's paradox ensues. As a consequence, Agda's type `Set` is not the type of
*all* types, but only the type of "small" types. Itself, the type `Set` is not
small, but instead "large". The type of `Set` is `Set₁`, the type of all large
types, which itself is not "large", but "very large". The type of `Set₁` is
`Set₂`, the type of all very large types, which itself is ..., and so on:

```
-- true : Bool : Set : Set₁ : Set₂ : …
```

In Agda, this story used to continue up to `Setω`, but in 2021, the universe
hierarchy was extended up to the (ω⋅2)'th level.
:::


## Example: Identity function

With the type of Booleans at hand, we can implement our first function, the
identity function which maps every input value to itself, i.e. which maps
`false` to `false` and `true` to `true`. As in Haskell, and unlike in most
other programming languages, no special keyword is needed to define a function.

Here is a template for the required code:

```
id : Bool → Bool
id x = {--}x{--}

-- Tests
-- EX: id false ≡ false
-- EX: id true  ≡ true
```

On the right hand side of the definition, we encounter our first "hole",
a placeholder displayed as `{!!}`. In Agda, we often build our programs or proofs
interactively; holes are the main interaction points. A hole can be created by
inserting a question mark `?` and then reloading the file using `C-c C-l` (i.e.
`Ctrl-c Ctrl-l`).

Follow the hints below to solve the first exercise, implementing the identity
function.

::: Hint :::
1. Fire up Agda by clicking on `Edit hole`.
2. Press `C-c C-l` to activate the hole.
3. Navigate to the hole.
4. Fill the hole with the following content: `x`
5. Press `C-c C-SPC` to verify that the proposed hole contents are type-correct.
6. Press `C-c C-l` to ask Agda to reload the file. You should then see a
   celebratory confetti animation, confirming that the exercise has been solved.
:::


## Example: Negation

As a second example, let's implement the negation function. It should map
`false` to `true` and vice versa:

```
not : Bool → Bool
-- Holify
not false = true
not true  = false

-- Tests
-- EX: not false ≡ true
-- EX: not true  ≡ false
```

Unlike most other programming languages, Agda does not have a built-in `if`
keyword; instead, we use *pattern matching* to define a function by cases.
Even better, we do not need to list all the possible cases on our own; we can
leverage Agda's assistive features to do that for us, as explained in the
hints.

::: Hint :::
1. First introduce a variable to the left of the `=` symbol, i.e. have the line
   begin with `not x`.
2. Reload the file using C-c C-l, so that the hole activates.
3. Then, ensuring that the cursor is inside the hole, press C-c C-c and answer
   that you would like to do the case split on the variable `x`.
4. Finally, for each case, fill in the definition. Press C-c C-SPACE when you
   are finished with a hole.
5. Ask Agda to reload the file again using C-c C-l. You should then see
   a confetti animation, indicating that the exercise has been successfully solved.
:::
