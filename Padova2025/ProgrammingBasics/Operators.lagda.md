```
module Padova2025.ProgrammingBasics.Operators where
```

# Operators

Let us begin by importing the definitions from the previous module:

```
open import Padova2025.ProgrammingBasics.Booleans
```

The `import` keyword causes the respective module to be loaded; by `open`,
all its definitions are brought into scope. Without `open`, we would need to
use `Padova2025.ProgrammingBasics.Booleans.Bool` to refer to the type of
Booleans.


## Example: Logical AND

The logical AND operator could be defined in Agda as follows, specifying one
clause for each of the four possible cases.

```
and : Bool → Bool → Bool
and false false = false
and false true  = false
and true  false = false
and true  true  = true
```

::: Aside :::
From blackboard mathematics, we might have expected the type signature to read
`and : Bool × Bool → Bool`. For now, let us not worry about this issue and just
accept the displayed syntax as Agda's way of introducing functions with two
parameters. We will later meet a a [satisfying
explanation](https://en.wikipedia.org/wiki/Currying).
:::

Here is how the operator could be used:

```
example-usage : Bool
example-usage = and false (and true false)
```

This piece of code looks a bit like Lisp. We can mimic blackboard notation more
closely by renaming the function `_&&_`. Semantically, nothing changes;
syntactically, the underscores indicate that the `_&&_` function should be used
as an infix operator with the arguments supplied to the left and the right.

```
infixr 6 _&&_
_&&_ : Bool → Bool → Bool
false && false = false
false && true  = false
true  && false = false
true  && true  = true
```

::: Aside :::
The first line in this snippet, `infixr 6 _&&_`, is optional and only included
to tell Agda how tightly our new operator should bind. For instance, later we
will provide `_+_` with precedence level 6 and `_*_` with precedence level `7`,
so that expressions like `a + b * c` are correctly parsed as `a + (b * c)`
instead of the incorrect `(a + b) * c`.
:::

We can then rewrite `example-usage` as follows.

```
example-usage' : Bool
example-usage' = false && (true && false)
```


## Exercise: Logical OR

In a similar vein, implement the logical OR operator.

```
infixr 5 _||_
_||_ : Bool → Bool → Bool
false || y = {--}y{--}
true  || y = {--}true{--}

-- Tests
-- EX: (false || false) ≡ false
-- EX: (false || true)  ≡ true
-- EX: (true  || false) ≡ true
-- EX: (true  || true)  ≡ true
```


## Exercise: A better definition of logical AND

The definition of `_&&_` offered above is needlessly complex. Instead of four
defining clauses, we can make do with two. Find this shorter alternative
definition.

```
_&&'_ : Bool → Bool → Bool
-- Holify
_&&'_ false y = false
_&&'_ true  y = y

-- Tests
module _ where private
  open import Padova2025.Equality.Definition

  test₁ : (y : Bool) → (false &&' y) ≡ false
  test₁ y = refl

  test₂ : (y : Bool) → (true &&' y) ≡ y
  test₂ y = refl
```

::: Aside :::
As a rule of thumb, function definitions which make do with fewer case
distinctions are better, because such definitions allow us to give shorter
proofs, as Agda is able to simplify terms to a larger extent. For instance,
while it is true that `false && y` is `false` for every value of `y`,
this fact is not evident to Agda and instead needs to be proven. For `_&&'_`,
in contrast, this identity is manifest.
:::
