```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Connectives.Existential where
```

# Existential quantification

A witness for an existential quantification "there exists a value `x : A` such
that `P x`" should be a pair consisting of a suitable value `x : A` and a
witnesses of type `P x`. Hence we introduce, for any type `A` and any
predicate `P : A → Set`, the following dependent pair type.

```code
infixr 4 _,_
data Σ (A : Set) (P : A → Set) : Set where
  _,_ : (fst : A) → (snd : P fst) → Σ A P
```

::: Aside :::
While this definition is just fine, we will actually use the following one.

```
open import Agda.Primitive

infixr 4 _,_
record Σ {ℓ ℓ' : Level} (A : Set ℓ) (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : P fst
open Σ public
```

The difference is twofold. Firstly, we use `record` instead of `data`. Record
types have the advantage that they support
[eta equality](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion):
Without having to pattern match on a value `w` of type `Σ A P`, such a value is
judgmentally equal to `(fst w , snd w)`.

Secondly, we allow the type `A` and the values of the `P` function to be larger
kinds of types, i.e. types in `Set₁` or higher, instead of restricting to the base
universe `Set`. This extra generality is useful for later developments. It
would be a nuisance to have to redefine the dependent pair construction then.
:::

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.EvenOdd
```

For instance, the type `Σ ℕ Even` is the type of witnesses that there exists an
even number. This type is populated by infinitely many inhabitants, such as the
following two.

```
there-exist-even-numbers : Σ ℕ Even
there-exist-even-numbers = (zero , base-even)

there-exist-even-numbers' : Σ ℕ Even
there-exist-even-numbers' = (two , two-even)
```


## Syntactic sugar

In blackboard mathematics, we write less succinctly but more evocatively
"$\exists(x \in \mathbb{N}).\ \mathrm{Even}(x)$" instead of `Σ ℕ Even`.
Thanks to a particular Agda feature, we can mimic this notation in Agda,
as we can define custom syntax:

::: More :::
```
infix 2 ∃-syntax
infix 2 Σ-syntax
∃-syntax : {ℓ ℓ' : Level} {A : Set ℓ} → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
∃-syntax = Σ _
Σ-syntax : {ℓ ℓ' : Level} (A : Set ℓ) → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
Σ-syntax = Σ
-- These are just ordinary functions, to be used in the syntax declarations below.

syntax ∃-syntax (λ x → P) = ∃[ x ] P
-- With this declaration, the right hand side (where `P` is an Agda term which
-- will usually contain `x` as a free variable) is an abbreviation for the left
-- hand side.

syntax Σ-syntax A (λ x → P) = Σ[ x ∈ A ] P
```
:::

We can then express existential disjunction as follows.

```
there-exist-even-numbers'' : ∃[ n ] Even n
there-exist-even-numbers'' = four , step-even two-even

there-exist-even-numbers''' : Σ[ n ∈ ℕ ] Even n
there-exist-even-numbers''' = succ (succ four) , step-even (step-even two-even)
```

It is a bit unfortunate that we cannot use the colon symbol and have to
resort to `∈`. Some people use the colon-lookalike `∶` (which is distinct
from the actual colon `:`), but this alternative is also confusing.


## Exercise: Tautologies involving existential quantification

```
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Connectives.Disjunction
```

```
infinitary-de-morgan₁ : {A : Set} {P : A → Set} → ((x : A) → ¬ P x) → ¬ (∃[ x ] P x)
-- Holify
infinitary-de-morgan₁ f (x , p) = f x p
```

```
infinitary-de-morgan₂ : {A : Set} {P : A → Set} → ¬ (∃[ x ] P x) → ((x : A) → ¬ P x)
-- Holify
infinitary-de-morgan₂ f x p = f (x , p)
```

```
∃-∨ : {A B : Set} {P : A → Set} → Σ[ x ∈ A ] (P x ⊎ B) → (Σ[ x ∈ A ] P x) ⊎ B
-- Holify
∃-∨ (x , left  p) = left  (x , p)
∃-∨ (x , right b) = right b
```


## Remark: A variety of formalizations of evenness

[Back when introducing
predicates](Padova2025.ProvingBasics.EvenOdd.html), we have chosen one
particular definition of evenness. But other formalizations are also
possible. Let us collect here all the auxiliary results showing that
several of those notions coincide.

```
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

```
Even₁ Even₂ Even₃ Even₄ : ℕ → Set

Even₁ n = Even n
Even₂ n = ¬ Odd n
Even₃ n = Odd (succ n)
Even₄ n = ∃[ m ] (n ≡ twice m)
```

```
1⇒2 : {n : ℕ} → Even₁ n → Even₂ n
2⇒1 : {n : ℕ} → Even₂ n → Even₁ n
1⇒3 : {n : ℕ} → Even₁ n → Even₃ n
3⇒1 : {n : ℕ} → Even₃ n → Even₁ n
1⇒4 : {n : ℕ} → Even₁ n → Even₄ n
4⇒1 : {n : ℕ} → Even₄ n → Even₁ n

1⇒2 = even-and-odd
2⇒1 = not-odd-implies-even _
1⇒3 = succ-even
3⇒1 = succ-even'
1⇒4 p = half _ , even-twice p
4⇒1 (m , p) = subst Even (sym p) (twice-even m)
```
