```
module Padova2025.ProvingBasics.Negation where
```

# Negation

In mathematical logic, the negation $\neg P$ of a proposition $P$ is defined as
"assuming $P$ implies a contradiction", that is as the implication $(P
\Rightarrow ↯)$.

To adopt this definition in Agda, we introduce a type `⊥` which does not have
any inhabitants:

```
data ⊥ : Set where   -- enter `⊥` by `\bot`
-- no constructors, so the type `⊥` is manifestly empty
```

Hence proving a negation $\neg P$ in Agda means to construct a function which
maps witnesses of $P$ to witnesses of ↯, i.e. to values of type `⊥`.

We can also introduce the negation symbol in Agda:

```
infix 3 ¬_
¬_ : Set → Set  -- enter `¬` as `\neg`
¬ P = (P → ⊥)
```


## Exercise: One is not even

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.EvenOdd
```

An immediate consequence from the definition of `Even`, but nevertheless quite
instructive at this point, is the result that the number `one` is not even.

```
one-not-even : Even one → ⊥
-- Holify
one-not-even ()
```

::: Hint :::
1. As usual, introduce a variable on the left of the `=` sign:
   `one-not-even p = {!!}`
2. Then, also as usual, press `C-c C-c` to ask Agda to do a case split on `p`.
3. Agda will then notice that there are no possible cases and indicate this
   observation with the *empty pattern* `()`.
:::


## Exercise: No simultaneously even and odd numbers

```
even-and-odd : {a : ℕ} → Even a → Odd a → ⊥
-- Holify
even-and-odd (step-even p) (step-odd q) = even-and-odd p q
```


## Exercise: An inductive type without a base case

Let us consider the following variant of the definition of the natural numbers:

```
data Weird : Set where
  succ : Weird → Weird
```

How many values of type `Weird` are there?

::: More :::
Given an inhabitant `x` of type `Weird`, its sole constructor `succ` could be
used to obtain the further inhabitant `succ x`. Applying `succ` again would
result in yet another inhabitant, and so on. But we do not have any inhabitants
to start with; the constructor `succ` is of no use; the type `Weird` is empty.

::: Aside :::
What about the infinite expression `succ (succ (succ (...)))`? Does this
expression not denote a value of type `Weird`?

No -- non-terminating expressions like these are not allowed for datatypes. Try
it:
```code
loop : Weird
loop = succ loop
```
Specific kinds of non-terminating expressions are possible for so-called
*co-datatypes*, but we will not discuss those here.
:::

We can formalize this observation in Agda as follows, expressing the following
implication: If there would be an inhabitant of `Weird`, then a contradiction
would ensue.

```
Weird-is-empty : Weird → ⊥
-- Holify
Weird-is-empty (succ x) = Weird-is-empty x
```
:::


## Exercise: Ex falso quodlibet

In (both classical and intutionistic, but not minimal) logic, from a
contradiction any statement follows. In Agda, we have the parallel fact
we have a function `⊥ → A` for any type `A`:

```
⊥-elim : {A : Set} → ⊥ → A
-- Holify
⊥-elim ()
```
