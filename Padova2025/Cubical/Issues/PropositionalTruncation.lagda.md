```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Cubical.Issues.PropositionalTruncation where
```

# Propositional truncation

```
open import Padova2025.ProvingBasics.Connectives.Existential
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
specified element `x : A` and a witness `p : B x`.  So a witness does
not only attest the fact that there merely is an element `x` such that
`B x`. Instead, it also explicitly specifies one possible such
element `x`. This is in contrast to the notion of existence from
blackboard mathematics, which is less informative and does not
disclose suitable elements.


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

```code
to do:
- doubly negated existence
- wannabe construction as HIT
- universe-jumping impredicative construction
```
