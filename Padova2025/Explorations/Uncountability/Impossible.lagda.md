```
module Padova2025.Explorations.Uncountability.Impossible where
```

# Seemingly impossible programs and proofs

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
import Padova2025.ProvingBasics.Equality.Booleans as B
```

::: Aside :::
Let us switch the [`with ... in ...` syntactic
sugar](https://agda.readthedocs.io/en/stable/language/with-abstraction.html#with-abstraction-equality)
on.
```
{-# BUILTIN EQUALITY _≡_ #-}
```
:::

Let us call a type `X` *searchable* iff decidable predicate `P : X → Bool`
has a root (attains the value `false`) or alternatively is constantly `true`.

```
Searchable : Set → Set
Searchable X = (P : X → Bool) → (∃[ x ] P x ≡ false) ⊎ ((x : X) → P x ≡ true)
```

In classical mathematics, every type is trivially searchable. But as
long as we do not postulate classical mathematics, this searchability
condition expresses in Agda a much stronger claim---namely that, given
a predicate `P`, we can *decide* by means of an algorithm which
alternative holds.

Equivalent (for inhabited types) is the following property related to
the [drinker paradox](https://en.wikipedia.org/wiki/Drinker_paradox).

```
HasDrinkers : Set → Set
HasDrinkers X = (P : X → Bool) → ∃[ a ] (P a ≡ true → ((x : X) → P x ≡ true))
```

```
false≢true : false ≢ true
false≢true ()
```

```
HasDrinkers⇒Searchable : {X : Set} → HasDrinkers X → Searchable X
-- Holify
HasDrinkers⇒Searchable find P with find P
... | a , p with P a in eq
... | false = left  (a , eq)
... | true  = right (p refl)
```

```
Searchable⇒HasDrinkers : {X : Set} → X → Searchable X → HasDrinkers X
-- Holify
Searchable⇒HasDrinkers x₀ dec P with dec P
... | left  (x , eq) = x  , λ eq' → ⊥-elim (false≢true (trans (sym eq) eq'))
... | right f        = x₀ , λ _   → f
```


## Exercise: The Booleans are searchable

Finite types such as `Bool` are searchable: To decide whether a
predicate has a root, we can inspect every element of the type in turn.

```
Bool-searchable : Searchable Bool
Bool-searchable P with P false in eq | P true in eq'
... | false | y     = {--}left  (false , eq){--}
... | true  | false = {--}left  (true  , eq'){--}
... | true  | true  = {--}right λ { false → eq ; true → eq' }{--}
```

There is also a slick proof involving the ideas of the
[cryptic `is-tautology₁'` function](Padova2025.ProvingBasics.Equality.Booleans.html#tautologies)
from the module on equality results on Booleans.

```
Bool-hasDrinkers : HasDrinkers Bool
Bool-hasDrinkers P = P false , {--}B.part₂ P{--}
```


## Infinite yet searchable types

Amazingly, beyond the finite types, *there do exist infinite types which are searchable*.

- In any flavor of constructive mathematics where
  [function extensionality](Padova2025.Cubical.Issues.FunctionExtensionality.html)
  is available, such as Cubical Agda, the "one-point compactification of the natural numbers",
  roughly speaking `ℕ` with an added point `∞`, is searchable.

- In some flavors, even the Cantor space is searchable---its uncountability notwithstanding.

This shocking fact has been thoroughly explored by Martín Escardó. To jump into this fascinating
area, have a look at [this classic post on Andrej Bauer's blog](https://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/),
[this Agda code](https://martinescardo.github.io/TypeTopology/TypeTopology.GenericConvergentSequenceCompactness.html) or
[these slides](https://www.ioc.ee/~tarmo/tsem16/escardo2605-slides.pdf).
