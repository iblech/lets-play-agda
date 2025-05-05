```
module Padova2025.ProgrammingBasics.SyntacticSugar where
```

# Syntactic sugar

In an effort to make Agda programming more pleasant, cut down on line noise and
mimic blackboard notation more closely, Agda supports a number of syntactical
convenience features. In this section we shall discuss some of them. They are
most useful when dealing with functions whose output type depends on the input
values.

We repeat two definitions from the [introduction to dependent
functions](Padova2025.ProgrammingBasics.DependentFunctions.html):

```
open import Padova2025.ProgrammingBasics.Naturals.Base

id : (X : Set) → X → X
id X a = a

example-usage : ℕ
example-usage = id ℕ four
```


## Marking parameters as implicit

In the definition of `example-usage` above, we had to explicitly write down the
type `ℕ`, even though Agda should be able to infer this type from the type of
the second argument, `four`, which is known to be of type `ℕ`.

Indeed, instead of writing down "`ℕ`", we can also use "`_`" as a placeholder, 
asking Agda to infer a suitable value:

```
example-usage' : ℕ
example-usage' = id _ four
```

::: Aside :::
If Agda does not manage to infer a value from the context, the corresponding
site will be colored yellow.
:::

We can improve on this situation even further and remove the first argument 
altogether. To this end, we mark the first parameter of `id` as *implicit*:

```
id-with-implicit-parameter : {X : Set} → X → X
id-with-implicit-parameter a = a

example-usage'' : ℕ
example-usage'' = id-with-implicit-parameter four
```

In case we want to explicitly specify the value of an implicit parameter, perhaps
to aid Agda or a human reader in understanding the code, or to narrow down the
space of possibilities so that error messages and interaction points become
more useful, we can use curly braces at the call site as an antidote for the
curly braces in the definition:

```
example-usage''' : ℕ
example-usage''' = id-with-implicit-parameter {ℕ} four
```


## Contracting parameter declarations

Let us consider the following type signature.

```code
K : (X : Set) → (Y : Set) → X → Y → X
```

This signature can be written up more succinctly in two ways. Firstly, we can
omit the function type arrow `→` between the parenthesized variable
declarations:

```code
K : (X : Set) (Y : Set) → X → Y → X
```

Secondly, as `X` and `Y` are of the same type, we can contract the declarations
as follows:

```code
K : (X Y : Set) → X → Y → X
```

::: Aside :::
To arrive at fully idiomatic Agda code, one would also mark `X` and `Y` as
implicit. The resulting function can then be used just as the corresponding
combinator in the [SKI calculus](https://en.wikipedia.org/wiki/SKI_combinator_calculus):

```code
K : {X Y : Set} → X → Y → X
```
:::
