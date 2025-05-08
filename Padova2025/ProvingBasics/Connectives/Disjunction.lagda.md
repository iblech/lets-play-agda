```
module Padova2025.ProvingBasics.Connectives.Disjunction where
```

# Disjunction

In the previous couple sections, we have already stated and proved quite a few
results. But we are still lacking the means to express other, quite basic,
assertions, such as the following:

1. **Every natural number is even or odd.** \
   $\forall(n \in \mathbb{N}).\ (\mathrm{Even}(n) \vee \mathrm{Odd}(n))$

2. **Every prime number greater than three is one more or one less than a multiple of six.** \
   $\forall(p \in \mathbb{P}).\ (p > 3 \Rightarrow (6 \mid p-1 \vee 6 \mid p+1))$

3. **Beyond every natural number, there is a prime number.** \
   $\forall(n \in \mathbb{N}).\ \exists(p \in \mathbb{N}).\ (p > n \wedge p \in \mathbb{P})$

The purpose of this module and the next ones is to fill this gap, and introduce disjunction (∨),
conjunction (∧) and existential quantification (∃). Following the [propositions
as types philosophy](Padova2025.ProvingBasics.PropositionsAsTypes.html), we
should for instance introduce a suitable type of witnesses that a given number `n`
is even or odd. The first result above would then be formalized by a function
which reads an arbitrary number `n` as input and outputs such a kind of
witness.


## Definition: Disjoint union

For expressing disjunction (∨), for given types `A` and `B` we introduce their
disjoint union `A ⊎ B`:

```
infixr 1 _⊎_
data _⊎_ (A : Set) (B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- In Haskell, `A ⊎ B` is known as `Either A B`.
```

In other words, the elements of `A ⊎ B` are of the form `left x` for some `x : A`,
or `right y` for some `y : B`. The computational reading is that `left` is a
function which inputs an element of type `A` and outputs an element of type `A
⊎ B`, and similarly with `right`. The logical reading is that `A` implies `A or B`.
The type of witnesses that a number `n` is even or odd is then `Even n ⊎ Odd n`.


## Exercise: Tautologies involving disjunction

```
open import Padova2025.ProvingBasics.Negation
```

```
∨-comm : {A B : Set} → A ⊎ B → B ⊎ A
-- Holify
∨-comm (left  x) = right x
∨-comm (right y) = left  y
```

```
∨-assoc : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
-- Holify
∨-assoc (left  (left  x)) = left  x
∨-assoc (left  (right y)) = right (left  y)
∨-assoc (right z)         = right (right z)
```

```
∨-elim : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
-- Holify
∨-elim f g (left  x) = f x
∨-elim f g (right y) = g y
```

```
∨-map : {A A' B B' : Set} → (A → A') → (B → B') → A ⊎ B → A' ⊎ B'
-- Holify
∨-map f g (left  x) = left  (f x)
∨-map f g (right y) = right (g y)
```

```
∨-codiag : {A : Set} → A ⊎ A → A
-- Holify
∨-codiag (left  x) = x
∨-codiag (right y) = y
```

```
∨-not₁ : {A : Set} → A ⊎ ⊥ → A
-- Holify
∨-not₁ (left  x)  = x
∨-not₁ (right ())
```

```
∨-not₂ : {A B : Set} → A ⊎ B → ¬ B → A
-- Holify
∨-not₂ (left  x) f = x
∨-not₂ (right y) f = ⊥-elim (f y)
-- Alternatively, the second clause can be written as follows.
-- ∨-not₂ (right y) f with f y
-- ... | ()
```


## Exercise: Even or odd

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.EvenOdd
```

```
even-or-odd : (x : ℕ) → Even x ⊎ Odd x
-- Holify
even-or-odd zero            = left base-even
even-or-odd (succ zero)     = right base-odd
even-or-odd (succ (succ x)) with even-or-odd x
... | left  p = left  (step-even p)
... | right p = right (step-odd p)
```

```
not-odd-implies-even : (x : ℕ) → ¬ Odd x → Even x
-- Holify
not-odd-implies-even x p = ∨-not₂ (even-or-odd x) p
```
