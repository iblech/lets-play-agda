```
module Padova2025.Explorations.Forcing.Cohen (X : Set) where
```

# Cohen forcing

```
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.Lists
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.ProvingBasics.Termination.Gas using (Maybe; nothing; just; lookupMaybe)
open import Padova2025.ProvingBasics.Connectives.Existential
```

The purpose of this module is to provide suitable definitions so that
we can explore a forcing extension of the base universe in which a
*generic infinite sequence of elements of `X`* exists, i.e. a *generic
function `f₀ : ℕ → X`*. This function will turn out to be distinct from
every function `ℕ → X` of the base universe; hence Cohen forcing
allows us to enlarge the base universe by a new function `ℕ → X`
(without changing the naturals or the given type `X`).

This new function is *generic* in the sense that, for every property
`P` of a certain kind, if `f₀` has it, then so does every function
`f : ℕ → X` from the base universe.


## Approximating by finite lists

For approximating an infinite sequence `ℕ → X`, we employ finite lists
of elements of `X` as [described in the
introduction](Padova2025.Explorations.Forcing.Intro.html#approximating-from-below).

```
L : Set
L = List X
```

Given a predicate `P : L → Set`, the next definition introduces a new
predicate `∇ P : L → Set`. The intuitive meaning of the assertion `∇ P
xs` is that, no matter how the finite approximation `xs` evolves over
time to a better approximation `ys`, eventually `P ys` will hold.
The operator `∇` is a so-called *modality*, more precisely the
*eventually modality*.

```
data ∇ (P : L → Set) : L → Set where
  now   : {xs : L} → P xs → ∇ P xs
  later : {xs : L} → ((x : X) → ∇ P (xs ∷ʳ x)) → ∇ P xs
```

As a basic example how this modality can be used, let us show that
no matter how the empty list `[]` evolves over time, eventually
it will be a list of length at least 3:

```
eventually-length-3 : ∇ (λ xs → length xs ≥ three) []
-- Holify
eventually-length-3 = later (λ a → later (λ b → later (λ c → now (s≤s (s≤s (s≤s z≤n))))))
```

Sometimes it is useful to leverage Agda's
[instance arguments feature](https://agda.readthedocs.io/en/stable/language/instance-arguments.html)
to lighten the notation. By defining...

```
cur : {{L}} → L
cur {{xs}} = xs

∇' : ({{L}} → Set) → (L → Set)
∇' P xs = ∇ (λ ys → P {{ys}}) xs
```

...we can rewrite the previous example as follows:

```
eventually-length-3' : ∇' (length cur ≥ three) []
-- Holify
eventually-length-3' = eventually-length-3
```

Arriving at a result of the form `∇ P xs` is not a dead end at all;
instead, we can reason "under the modality" as follows.

```
_>>=_ : {P Q : L → Set} {xs : L} → ∇ P xs → ({ys : L} → P ys → ∇ Q ys) → ∇ Q xs
now   p >>= k = k p
later f >>= k = later λ x → f x >>= k
```


### Exercise: Eventually arbitrarily long

Prove for every number `n` that the empty list eventually evolves to a
list of length at least `n`.

```
eventually-length : (n : ℕ) → ∇' (length cur ≥ n) []
eventually-length zero     = {--}now z≤n{--}
eventually-length (succ n) = eventually-length n >>= λ len≥n →
  {--}later λ x →
    now (≤-trans (succ-monotone len≥n) (≡⇒≤ (sym (length-snoc _ x)))){--}
```


## Constructing the generic sequence

We cannot directly introduce the generic sequence `f₀` as an actual
function of type `ℕ → X`, as the type `ℕ → X` contains only the
functions of the base universe. But we can define what it means for
the equation `f₀ n ≡ x` to hold. As this assertion is about `f₀`,
from the point of view of the base universe its truth value will
depend on the current approximation:

```
f₀[_]≡_ : {{L}} → ℕ → X → Set
f₀[ n ]≡ x = lookupMaybe cur n ≡ just x
```

To talk about the generic sequence `f₀`, which only really exists
in the forcing extension, from the point of view of the base universe,
we need to keep track of the current approximation, and in the case
of atomic propositions, bottom, disjunction and existential quantification
also be prepared to let the current approximation evolve to a better one.

For instance, here is how we express that `f₀` is defined on every input
(even though no single finite approximation is):

::: More :::
```
lemma-lookup : {A : Set} → (xs : List A) (n : ℕ) → length xs > n → ∃[ x ] (lookupMaybe xs n ≡ just x)
-- Holify
lemma-lookup (x ∷ xs) (zero)   p       = x , refl
lemma-lookup (x ∷ xs) (succ n) (s≤s p) = lemma-lookup xs n p
```
:::

```
f₀-total : (n : ℕ) → ∇' (∃[ x ] (f₀[ n ]≡ x)) []
-- Holify
f₀-total n = eventually-length (succ n) >>= λ len>n → now (lemma-lookup _ _ len>n)
```


## Genericity of the generic sequence

```code
generic⇒actual : {P : L → Set} → {f : ℕ → X} → ∇ P [] → ∃[ n ] (P (map f (upTo n)))
generic⇒actual p = {!!}
```
