```
module Padova2025.ProvingBasics.Equality.Reasoning where
```

# Equational reasoning

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

The equality proofs we have discussed before have been put in so-called
*combinatorial style*, making use of the *combinators*
[`trans`](Padova2025.ProvingBasics.Equality.General.html#trans),
[`sym`](Padova2025.ProvingBasics.Equality.General.html#sym) and
and [`cong`](Padova2025.ProvingBasics.Equality.General.html#cong). While proofs
in this style are not too unreasonable to construct, if one makes extensive use
of Agda's assistive features, the resulting proofs are often hard to read. Such
"write-only" proofs constitute an antithesis to the ideals of elegance we are
striving for when playing Agda. They also look totally unlike usual blackboard
proofs of identities.

Instead, on a blackboard, we usually verify identities by chains of
equalities, using `trans` implicitly rather than explicitly. This style is
called *equational reasoning*, and it is also available in Agda. For instance,
here is how the [proof of commutativity of addition](Padova2025.ProvingBasics.Equality.NaturalNumbers.html#+-comm)
like in this style.

```
open import Padova2025.ProvingBasics.Equality.Reasoning.Core
-- not magic, but nevertheless recommended to skip on first reading

+-comm' : (a b : ℕ) → a + b ≡ b + a
+-comm' zero     b = sym (+-zero b)
+-comm' (succ a) b = begin
  succ a + b   ≡⟨⟩
  succ (a + b) ≡⟨ cong succ (+-comm' a b) ⟩
  succ (b + a) ≡⟨ sym (+-succ b a) ⟩
  b + succ a   ∎
```

We start with the left-hand side and then repeatedly carry out manipulations
until we arrive at the right-hand side. Steps indicated by `≡⟨⟩` hold by
definition (by [`refl`](Padova2025.ProvingBasics.Equality.Base.html#_≡_.refl)).
Steps indicated by `≡⟨ p ⟩` hold by the specified reason (element of the
corresponding identity type) `p`.

::: Aside :::
Instead of `≡⟨ sym p ⟩`, one can also write `≡˘⟨ p ⟩`.
:::


## Exercise: Distributivity, revisited

Redo the [earlier proof](Padova2025.ProvingBasics.Equality.NaturalNumbers.html#·-distribʳ-+)
of distributivity in equational style.

```
·-distribʳ-+' : (a b c : ℕ) → (a + b) · c ≡ a · c + b · c
-- Holify
·-distribʳ-+' zero     b c = refl
·-distribʳ-+' (succ a) b c = begin
  (succ a + b) · c    ≡⟨⟩
  succ (a + b) · c    ≡⟨⟩
  c + (a + b) · c     ≡⟨ cong (c +_) (·-distribʳ-+' a b c) ⟩
  c + (a · c + b · c) ≡˘⟨ +-assoc c (a · c) (b · c) ⟩
  (c + a · c) + b · c ≡⟨⟩
  succ a · c  + b · c ∎
```
