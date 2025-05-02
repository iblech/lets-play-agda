```
module Padova2025.ProvingBasics.Equality.NaturalNumbers where
```

# Results on natural numbers

```
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```


## Exercise: Associativity of addition

```
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
-- Holify
+-assoc zero     b c = refl
+-assoc (succ a) b c = cong succ (+-assoc a b c)
```


## Exercise: Commutativity of addition

Establishing commutativity is a little bit more involved than establishing
associativity. Recall that the definition of addition involved a somewhat
arbitrary choice of whether to case split on the first or on the second argument.
The key idea in the commutativity proof developed in this exercise is to
establish that the other choice would have worked as well.

```
+-zero : (a : ℕ) → (a + zero) ≡ a
-- This does not hold by definition, the definition would state zero + b = b.
-- Holify
+-zero zero     = refl
+-zero (succ a) = cong succ (+-zero a)
```

```
+-succ : (a b : ℕ) → a + succ b ≡ succ (a + b)
-- This does not hold by definition, the definition would state succ a + b = succ (a + b).
-- Holify
+-succ zero     b = refl
+-succ (succ a) b = cong succ (+-succ a b)
```

```
+-comm : (a b : ℕ) → a + b ≡ b + a
-- Holify
+-comm zero     b = sym (+-zero b)
+-comm (succ a) b =
  trans (cong succ (+-comm a b)) (sym (+-succ b a))
```


## Exercise: Two ways of doubling

```
two-+-+ : (a : ℕ) → a + a ≡ two · a
-- Holify
two-+-+ a = cong (a +_) (sym (+-zero a))
```


## Exercise: Distributivity

```
·-distribʳ-+ : (a b c : ℕ) → (a + b) · c ≡ a · c + b · c
-- Holify
·-distribʳ-+ zero     b c = refl
·-distribʳ-+ (succ a) b c =
  trans (cong (c +_) (·-distribʳ-+ a b c)) (sym (+-assoc c (a · c) (b · c)))
```

A word of warning: The proof here will only barely be readable. When we
introduce *equational reasoning*, we will be able to format this proof in a
much more accessible manner.


## Exercise: One not zero, revisited

```
open import Padova2025.ProvingBasics.Negation
```

[Earlier we have informally
argued](Padova2025.ProvingBasics.Equality.FirstSteps.html#example-one-not-zero) that
there is no value of type `one ≡ zero`. Now let us formally prove that if there
was such a value, a contradiction would ensue.

```
one≠zero : ¬ (one ≡ zero)
-- Holify
one≠zero ()
```

As a corollary, prove that it is not the case that for all numbers `a`, `succ
(pred a)` is the same as `a`:

```
lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = {--}one≠zero (f zero){--}
```

Instead, the equation $\mathrm{succ}(\mathrm{pred}(a)) = a$ only holds for
positive numbers. State and prove this fact, making use of [the predicate
`IsPositive` from before](Padova2025.ProvingBasics.EvenOdd.html#IsPositive).

```
open import Padova2025.ProvingBasics.EvenOdd
```

```
lemma-succ-pred' : (a : ℕ) → {--}IsPositive a{--} → succ (pred a) ≡ a
-- Holify
lemma-succ-pred' a (case-succ _) = refl
```


## Exercise: Injectivity of successor

Prove that the successor function is injective:

```
succ-injective : {n m : ℕ} → succ n ≡ succ m → n ≡ m
-- Holify
succ-injective = cong pred
```


## Exercise: Twice even

State and prove that for every number `a`, the number
[`twice a`](Padova2025.ProgrammingBasics.DependentFunctions.html#twice) is even.

```
open import Padova2025.ProgrammingBasics.DependentFunctions
```

```
twice-even : (a : ℕ) → Even (twice a)
-- Holify
twice-even zero     = base-even
twice-even (succ a) = step-even (twice-even a)
```

::: Hint :::
1. First introduce a variable `a` in front of the `=` symbol and then
   reload the file using `C-c C-l`, so that the line reads `twice-even a =
   {!!}`.
2. Then use `C-c C-c` to ask Agda to case split on the variable `a`.
3. Navigate into the first hole and press `C-c ,` to obtain a summary of the
   situation.
4. Notice that `base-even` fits the bill (or use Agda's automatic mode, `C-c C-a`).
   Press `C-c C-SPACE` to conclude.
5. Now navigate to the second hole and inspect the situation with `C-c ,`.
6. Recognize that we are asked to verify the evenness of a number of the form
   `succ (succ _)`. Hence use the `step-even` constructor, write `step-even ?`
   into the hole and press `C-c C-SPACE`.
7. In the new hole, press `C-c ,` to get hold of the changed situation.
8. Notice that the recursive call `twice-even a` (in blackboard mathematics
   that would be an appeal to the induction hypothesis) fits the bill.
   Conclude by `C-c C-SPACE` followed by `C-c C-l`.
:::

The following exercise is similar but more involved. We will require the
[`subst` function](Padova2025.ProvingBasics.Equality.General.html#subst).

```
twice-even' : (a : ℕ) → Even (a + a)
-- Holify
twice-even' zero     = base-even
twice-even' (succ a) =
  subst Even lemma (step-even (twice-even' a))
  where
  lemma : succ (succ (a + a)) ≡ succ (a + succ a)
  lemma = cong succ (sym (+-succ a a))
```


## Exercise: Even twice

Conversely, let us prove that even numbers are of the form `twice a`, more
preceisely let us prove:

```
even-twice : {x : ℕ} → Even x → x ≡ twice (half x)
-- Holify
even-twice base-even     = refl
even-twice (step-even p) = cong (λ a → succ (succ a)) (even-twice p)
```


## Exercise: An impossible twice situation

```
impossible-twice : {x y : ℕ} → twice x ≡ succ (twice y) → ⊥
-- Holify
impossible-twice {succ x} {y} p = impossible-twice (sym (succ-injective p))
```


## Exercise: Twice as a homomorphism

```
twice-homo : (x y : ℕ) → twice (x + y) ≡ twice x + twice y
-- Holify
twice-homo zero     y = refl
twice-homo (succ x) y = cong succ (cong succ (twice-homo x y))
```


## Exercise: Injectivity of twice

```
twice-injective : {x y : ℕ} → twice x ≡ twice y → x ≡ y
-- Holify
twice-injective {zero}   {zero}   p = p
twice-injective {succ x} {succ y} p = cong succ (twice-injective (succ-injective (succ-injective p)))
```


## Exercise: Two deciders of evenness

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProvingBasics.Equality.Booleans
```

Back in [the section on decision
procedures](Padova2025.ProgrammingBasics.Naturals.DecisionProcedures.html),
we have discussed the function `even? : ℕ → Bool`, which has the purpose of
returning `true` if the input number is even, and `false` otherwise.

We can imagine at least two implementations of `even?`:

```
even?₁ : ℕ → Bool
even?₁ zero            = true
even?₁ (succ zero)     = false
even?₁ (succ (succ n)) = even?₁ n

even?₂ : ℕ → Bool
even?₂ zero     = true
even?₂ (succ n) = not (even?₂ n)
```

In this exercise, verify that these two implementations yield the same result on all inputs.

```
even?₁-even?₂ : (a : ℕ) → even?₁ a ≡ even?₂ a
-- Holify
even?₁-even?₂ zero            = refl
even?₁-even?₂ (succ zero)     = refl
even?₁-even?₂ (succ (succ a)) = trans (even?₁-even?₂ a) (sym (not² (even?₂ a)))
```
