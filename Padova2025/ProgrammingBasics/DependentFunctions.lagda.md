```
module Padova2025.ProgrammingBasics.DependentFunctions where
```

# Dependent functions

For most functions in blackboard mathematics and ordinary programming, the
result type is independent of the input value. For instance, no matter the
value of `n`, [`half n`](Padova2025.ProgrammingBasics.Naturals.Arithmetic.html#half)
is always of type `ℕ`. Similarly, to matter the value of `x`,
[`not x`](Padova2025.ProgrammingBasics.Booleans.html#not) is always of type `Bool`.

But there are also functions where the result type does depend on the input
value. A basic example is the so-called *polymorphic identity function*. Unlike
[`idBool : Bool → Bool`](Padova2025.ProgrammingBasics.Booleans.html#idBool) or
`idℕ : Nat → Nat`, the polymorphic identity function works at all types.

More precisely, the polymorphic identity function takes as input...

1. a value `X : Set` and
2. a value `a : X`,

and then returns the same value `a`. So the result type depends on the value of
the input `X`. In Agda we write this up as follows.

```
id : (X : Set) → X → X
id X a = a
```

We could then use this function as follows.

```
open import Padova2025.ProgrammingBasics.Naturals.Base

example-usage : ℕ
example-usage = id ℕ four
```

We will shortly define the type [`Vector A n`](Padova2025.ProgrammingBasics.Vectors.html)
of length-`n` lists of elements of `A`. We could then imagine the following
example for a dependent function:

```code
replicate : (A : Set) → (n : ℕ) → A → Vector A n
-- Read a type `A`, a number `n`, an element `x : A` as input
-- and output a length-`n` list of copies of `x`.

five-dimensional-zero-vector      = repliacte ℕ 5 zero
three-dimensional-all-ones-vector = replicate ℕ 3 one
```

::: Aside :::
Some people prefer to use the notation for dependent functions also in the
non-dependent case. They can:

```
twice : (x : ℕ) → ℕ
twice zero     = zero
twice (succ x) = succ (succ (twice x))
```
:::


## Example: Polymorphic constant function

Implement a function `K` which reads as input...

1. a type `X` (i.e. a value `X : Set`),
2. a type `Y`,
3. a value `x : X` and
4. a value `y : Y`,

... and returns `x`.

```
K : {--}(X : Set) → (Y : Set) → X → Y → X{--}
-- Holify
K X Y x y = x

-- Tests
-- EX: K ℕ ℕ zero one ≡ zero
```

```
import Padova2025.ProgrammingBasics.DependentFunctions.SyntacticSugar
```
