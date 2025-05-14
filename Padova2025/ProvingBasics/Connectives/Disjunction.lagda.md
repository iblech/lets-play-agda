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
function which inputs an element of type `A` and outputs an element of type `A ⊎ B`,
and similarly with `right`. The logical reading is that `A` implies `A or B`.
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


## Exercise: Successor of predecessor, revisited

```
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base
```

[We have already examined](Padova2025.ProvingBasics.Equality.NaturalNumbers.html#lemma-succ-pred')
the equation $\mathsf{succ}(\mathsf{pred}(a)) = a$, which only holds for
positive natural numbers. Let us now prove the following variant:

```
lemma-succ-pred'' : (a : ℕ) → succ (pred a) ≡ a ⊎ a ≡ zero
-- Holify
lemma-succ-pred'' zero     = right refl
lemma-succ-pred'' (succ a) = left  refl
```


## Exercise: Decidability of equality

```
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
open import Padova2025.ProgrammingBasics.HigherOrder
```

Every natural number is either zero, or not. This assertion is trivial
in classical mathematics for general logical reasons, as it is just an
instance of the [law of excluded middle](https://en.wikipedia.org/wiki/Law_of_excluded_middle)
($A ∨ ¬A$). But there is also a direct proof, a proof which we can implement
in Agda without having to postulate the law of excluded middle
and thereby destroying Agda's by-default constructive mode.

```
zero? : (x : ℕ) → (x ≡ zero) ⊎ ¬ (x ≡ zero)
-- Holify
zero? zero     = left  refl
zero? (succ x) = right λ ()
```

Unlike a proof relying on the law of excluded middle, this proof can
be *run*---try it, within the Agda editing session, press `C-c C-v`
and then input something like `zero? four`. The `zero?` function will
then determine whether `four` is zero, and compute a corresponding
witness.

::: Aside :::
This proof is a rare instance of an induction proof where the
induction step does not use the induction hypothesis.
:::

More generally, we have the result that any two numbers are equal or not:

```
eq? : (a b : ℕ) → (a ≡ b) ⊎ ¬ (a ≡ b)
-- Holify
eq? zero     zero     = left refl
eq? zero     (succ b) = right λ ()
eq? (succ a) zero     = right λ ()
eq? (succ a) (succ b) = ∨-map (cong succ) (λ f → f ∘ succ-injective) (eq? a b)
-- Alternatively:
-- eq? (succ a) (succ b) with eq? a b
-- ... | left  a≡b = left (cong succ a≡b)
-- ... | right a≢b = right λ p → a≢b (succ-injective p)
```


## Exercise: An oracle in the double negation monad

The following two tautologies are of supreme importance for the purpose of
extracting constructive content from classical proofs, and also quite cryptic
on first encounter.

```
¬¬-oracle : {A : Set} → ¬ ¬ (A ⊎ ¬ A)
-- Holify
¬¬-oracle f = f (right (λ x → f (left x)))
```

```
¬¬-bind : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
-- Holify
¬¬-bind m f = λ k → m (λ x → f x k)
```


## Exercise: Law of excluded middle and double negation elimination

```
LEM⇒DNE : ((A : Set) → A ⊎ ¬ A) → ((B : Set) → ¬ ¬ B → B)
-- Holify
LEM⇒DNE p B m with p B
... | left   a = a
... | right ¬a = ⊥-elim (m ¬a)
```

```
DNE⇒LEM : ((B : Set) → ¬ ¬ B → B) → ((A : Set) → A ⊎ ¬ A)
-- Holify
DNE⇒LEM p A = p (A ⊎ ¬ A) ¬¬-oracle
```
