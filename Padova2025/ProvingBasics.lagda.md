```
module Padova2025.ProvingBasics where
```

# Agda as a proof language

Here are a couple of facts about even and odd numbers. None of them are
particularly earth-shattering. How can we express these assertions in Agda, and
how can we prove them? How do we switch Agda from "programming mode" to "logic mode"?

<!-- update EvenOdd.lagda.md in case numbering changes -->

1. **Zero is an even number.** \
   $\mathrm{Even}(0)$

   ::: More :::
   ```code
   base-even    : Even zero
   "base-even is a witness that zero is even."
   ```
   :::

2. **If $a$ is even, then so is $a+2$.** \
   $\forall(a \in \mathbb{N}).\ (\mathrm{Even}(a) \Rightarrow \mathrm{Even}(a+2))$

   ::: More :::
   ```code
   step-even    : (a : ℕ) → Even a → Even (succ (succ a))
   "step-even is a function which reads as input
   - a number `a` and
   - a witness that `a` is even,
   and outputs
   - a witness that `succ (succ a)` is even."
   ```
   :::

3. **The sum of even numbers is even.** \
   $\forall(a,b \in \mathbb{N}).\ ((\mathrm{Even}(a) \wedge \mathrm{Even}(b)) \Rightarrow \mathrm{Even}(a+b))$

   ::: More :::
   ```code
   sum-even     : (a : ℕ) → (b : ℕ) → Even a → Even b → Even (a + b)
   "sum-even is a function which reads as input
   - a number `a`,
   - a number `b`,
   - a witness that `a` is even and
   - a witness that `b` is even,
   and outputs
   - a witness that `a + b` is even."
   ```
   :::

4. **The successor of an even number is an odd number.** \
   $\forall(a \in \mathbb{N}).\ (\mathrm{Even}(a) \Rightarrow \mathrm{Odd}(a+1))$

   ::: More :::
   ```code
   succ-even    : (a : ℕ) → Even a → Odd (succ a)
   "succ-even is a function which reads as input
   - a number `a` and
   - a witness that `a` is even,
   and outputs
   - a witness that `succ a` is odd."
   ```
   :::

5. **No number is simultaneously even and odd.** \
   **If a number $a$ is simultaneously even and odd, then a contradiction follows.** \
   $\forall(a \in \mathbb{N}).\ ((\mathrm{Even}(a) \wedge \mathrm{Odd}(a)) \Rightarrow ↯)$

   ::: More :::
   ```code
   even-and-odd : (a : ℕ) → Even a → Odd a → ⊥
   "even-and-odd is a function which reads as input
   - a number `a`,
   - a witness that `a` is even and
   - a witness that `a` is odd,
   and outputs
   - a witness of a contradiction."
   ```
   :::

Amazingly, Agda unifies the social activities of programming and proving. There
is no "logic mode" separate from "programming mode". Instead, a common language
is used for both.

This feat is made possible by *dependent types*. Unlike familiar types like `ℕ`
or `List ℕ` or `ℕ → ℕ` which exist in most statically typed programming
languages, dependent types are types which depend on values. Perhaps the most
well-known example of such a type is `Vector n X`, the type of length-`n` lists
of elements of `X`, where `n` can be an unknown value determined only at
runtime.

The key insight for formalizing the displayed assertions about even and odd
numbers is the following: **For each number `n`, we can set up a dependent type
`Even n` containing so-called *witnesses* that the number `n` is even.** We do
that in such a way that for those numbers `n` which are not even, the resulting
type `Even n` will be empty. Only for those numbers `n` which are even, the
resulting type will be inhabited.

The displayed assertions can then be formalized by suitable constant witnesses
or functions manipulating such witnesses---click on the buttons above to see
how.

Having formalized the assertions, we are now in a position to prove them.

```
open import Padova2025.ProvingBasics.EvenOdd
```
