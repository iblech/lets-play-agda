```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Cubical.Issues.PropositionalTruncation where
```

# Propositional truncation

```
open import Agda.Primitive
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.EvenOdd
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Termination.Ordering
```

It is time to confess: What we have defined in the
[Padova2025.ProvingBasics.Connectives.Existential
module](Padova2025.ProvingBasics.Connectives.Existential.html) as the
existential quantifier is not really the existential quantifier from
blackboard mathematics, and similarly our disjunction is not really
the disjunction from blackboard mathematics.

Our notion of existence is more precisely called "specified
existence", whereas the blackboard's notion of existence is "mere
existence": According to our definition, a witness of an existential
claim is a value of type `Σ[ x ∈ A ] B x`, so a pair consisting of a
specified element `x : A` and a witness `p : B x`. So a witness does
not only attest the fact that there merely is an element `x` such that
`B x`. Instead, it also explicitly specifies one possible such
element `x`. This is in contrast to the notion of existence from
blackboard mathematics, which is less informative and does not
disclose suitable elements.

This makes a difference when using an existential assumption to
construct mathematical objects. If the hypothesis is specified
existence, the result of our construction may depend on `x`.
If the hypothesis is mere existence, it may not.

In the following, we will write mere existence as `∥ Σ[ x ∈ A ] B x ∥`
(keeping in mind that standard Agda does not support this).


## Propositions as some types

We can make this more precise by introducing the term *proposition*
for those types whose values are all equal:

```
isProp : {ℓ : Level} → Set ℓ → Set ℓ
isProp X = (a b : X) → a ≡ b
```

For a type satisfying `isProp`, the only interesting thing is
whether it is inhabited.

For instance, for every number `n`, the type `Even n` of witnesses
that `n` is even is a proposition:

```
Even-isProp : (n : ℕ) → isProp (Even n)
-- Holify
Even-isProp _ base-even     base-even     = refl
Even-isProp _ (step-even p) (step-even q) = cong step-even (Even-isProp _ p q)
```

In contrast, the type `Σ[ x ∈ A ] B x` is typically not a proposition.


## Elimination principles

For specified existence, we have the following elimination principle:
"If, given an element `x : A` and a witness `p : B x`, we have a way
of contructing an element of type `R`, then we also have a way of
constructing such an element from the assumption `Σ[ x ∈ A ] B x`."

```
Σ-elim : {A : Set} {B : A → Set} {R : Set} → ((x : A) → B x → R) → (Σ[ x ∈ A ] B x → R)
-- Holify
Σ-elim f (x , p) = f x p
```

For mere existence, which standard Agda does not have, we only have
the following weaker principle:

```code
mere-existence-elim : {A : Set} {B : A → Set} {R : Set} → isProp R → ((x : A) → B x → R) → (∥ Σ[ x ∈ A ] B x ∥ → R)
```

In contrast to `Σ-elim`, the elimination principle for mere existence
requires the result type `R` to be a proposition.

A fine point for both kinds of existence, not expressed in the type signatures of
`Σ-elim` and the (fictitious, in standard Agda) `mere-existence-elim`
above, is that the result type `R` does not need to belong to the base
universe `Set`. It could also be a larger type, living in `Set₁`,
`Set₂` or beyond.


## The axiom of choice?

The difference between the two notions of existence is especially
visible in the interaction with functions. For instance, the following
statement looks a bit like the axiom of choice---well-known as
a cornerstore of *classical* foundations of mathematics. Hence it
should not be provable in standard Agda, which by default is constructive.
However, it is:

```
kinda-looking-like-the-axiom-of-choice
  : {A B : Set} {R : A → B → Set}
  → ((x : A) → Σ[ y ∈ B ] R x y)
  → Σ[ f ∈ (A → B) ] ((x : A) → R x (f x))
-- Holify
kinda-looking-like-the-axiom-of-choice p
  = (λ x → fst (p x)) , (λ x → snd (p x))
```

With our definitions, a witness of a statement "∀x:A. ∃y:B. R x y" is already
a function inputting an element `x : A` and outputting a pair consisting of
a suitable element `y : A` and a witness of `R x y`. Transforming such a witness
into a choice function is just a matter of repackaging the provided information;
formulated with specified existence instead of mere existence, choice is not
a principle with far-reaching consequences, but simply a constructive tautology.


## An impredicative fallback

Cubical Agda will allow us, for every type `A : Set`, to construct its
*propositional truncation* `∥ A ∥ : Set`, the reflection of `A` in the
world of propositions. The construction will look like this:

```code
-- a "higher inductive type"; only available in cubical mode
data ∥_∥ (A : Set) : Set where
  ∣_∣    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y
```

So the truncation `∥ A ∥` will be like `A`, but with extra identifications,
forcing `∥ A ∥` to be a proposition. It can be pictured as the quotient of `A`
by the equivalence relation which deems any two elements equivalent.

In standard Agda, we can approximate propositional truncation by an impredicative
encoding---at the price of having to jump to the next universe level.

```
-- impredicative fallback to true propositional truncation in standard Agda
∥_∥ : Set → Set₁
∥ A ∥ = ({R : Set} → isProp R → (A → R) → R)
```

This approximation validates the desired elimination principle by
definition, though only for result types `R` which live in the base
universe `Set`:

```
∥∥-elim : {A : Set} {R : Set} → isProp R → (A → R) → (∥ A ∥ → R)
-- Holify
∥∥-elim p f x = x p f
```

Cubical Agda's definition of propositional truncation as a higher
inductive type would support the following stronger principle:

```code
-- referring to the true ∥_∥, not the impredicative approximation
∥∥-elim : {ℓ : Level} {A : Set} {R : Set ℓ} → isProp R → (A → R) → (∥ A ∥ → R)
```

The impredicative approximation to the true propositional truncation
is definitely useful, though the restricted elimination principle is a
serious limitation, especially in view of the fact that the truncation
itself does not live in the base universe; nested applications of
our approximation will run into issues.

Another (quite embarassing) deficiency of our approximation to
propositional truncation is that it fails to produce a
proposition. Function extensionality would be required for
`isProp (∥ A ∥)`.


<!--

## Specified existence from mere existence

```
open import Padova2025.Cubical.Issues.FunctionExtensionality
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Operators
```

In general, we cannot deduce specified existence of an element `x : A`
such that `B x` from mere existence of such an element; specified
existence is much stronger. But there are exceptional situations where
we can explicitly reconstruct a suitable element `x` from the mere
knowledge of the existence such an element. One such situation is
the following.

Let `A` be the type of natural numbers and let `B : ℕ → Set`
be a decidable proposition. Then from mere existence of a number `x`
such that `B x` we can find, by checking each number up to `x`
in turn, the minimal such number. Unlike an arbitrary witness,
the minimum is unique; this is what allows us to go from mere
existence to specified existence.

```
falseUpTo? : (B? : ℕ → Bool) → ℕ → Bool
falseUpTo? B? zero     = true
falseUpTo? B? (succ n) = not (B? n) && falseUpTo? B? n
```

```
Min : (B? : ℕ → Bool) → ℕ → Set
Min B? n = B? n ≡ true × falseUpTo? B? n ≡ true
```

```code
ΣMin-isProp : (B? : ℕ → Bool) → isProp (Σ[ n ∈ ℕ ] Min B? n)
ΣMin-isProp B? (n , p) (n' , p') = {!!}
```

```code
find-min : (B? : ℕ → Bool) → Σ[ x ∈ ℕ ] B? x ≡ true → Σ[ x ∈ ℕ ] Min B? x
find-min B? (x , eq) = {!!}
```

```code
mere-implies-specified
  : (B? : ℕ → Bool)
  → ∥ Σ[ x ∈ ℕ ] B? x ≡ true ∥ → Σ[ x ∈ ℕ ] B? x ≡ true
mere-implies-specified B? p with ∥∥-elim (ΣMin-isProp B?) (find-min B?) p
... | (n , eq , _) = n , eq
```

-->


## Anonymous existence

TODO
