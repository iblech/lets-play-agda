```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Explorations.Forcing.Cohen (X : Set) (x₀ : X) where
```

# Cohen forcing

```
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Negation
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

withInstance : ({{L}} → Set) → (L → Set)
withInstance P xs = P {{xs}}
```

...we can rewrite the previous example as follows:

```
eventually-length-3' : ∇' (length cur ≥ three) []
-- Holify
eventually-length-3' = eventually-length-3
```


### Exercise: Bind operator

Arriving at a result of the form `∇ P xs` is not a dead end at all;
instead, we can reason "under the modality" as follows.

```
_>>=_ : {P Q : L → Set} {xs : L} → ∇ P xs → ({ys : L} → P ys → ∇ Q ys) → ∇ Q xs
-- Holify
_>>=_ (now   p) k = k p
_>>=_ (later f) k = later λ x → f x >>= k
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
the equation `f₀ n ≡ x` to hold. From the point of view of the forcing
extension, this will be an assertion just like any other and in
particular will have a truth value like any other. From the point of
view of the base universe however, the truth value of this assertion will
depend on the current approximation:

```
f₀[_]≡_ : {{L}} → ℕ → X → Set
f₀[ n ]≡ x = lookupMaybe cur n ≡ just x
```

To talk about the generic sequence `f₀`, which only really exists
in the forcing extension, from the point of view of the base universe,
we need to keep track of the current approximation and be prepared to
let the current approximation evolve to a better one.

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


## Implication and negation in the forcing extension

Let `P` and `Q` be two approximation-dependent propositions,
i.e. functions of type `L → Set`. What should it mean that `P`
implies `Q`?  More precisely, given an approximation `xs`, what should
it mean that `P` implies `Q` on stage `xs`?

One option would be given by the following straightforward definition,
which however we reject.

```
_⇒-naive_ : (L → Set) → (L → Set) → (L → Set)
P ⇒-naive Q = λ xs → P xs → Q xs
-- rejected proposal
```

This definition does not account for possibility of `xs` evolving
to better approximations. The established definition fixes this issue:

```
_⇒_ : (L → Set) → (L → Set) → (L → Set)
P ⇒ Q = λ xs → (ys : L) → P (xs ++ ys) → Q (xs ++ ys)
```

Similarly, a principled definition of the forcing extension's bottom
proposition would not be this...

```
⫫-naive : L → Set
⫫-naive xs = ⊥
```

...but this:

```
⫫-principled : L → Set
⫫-principled xs = ∇' ⊥ xs
-- fully spelled out: ⫫ xs = ∇ (λ ys → ⊥) xs
```

But as we have assumed, in the very beginning of this file, that the type `X`
is inhabited (by some element `x₀`), the two definitions are actually equivalent,
and hence we will adopt the simpler one for the remaining development.

```
⫫ : L → Set
⫫ = ⫫-naive
```

```
escape : {R : Set} {xs : L} → ∇' R xs → R
-- Holify
escape (now   p) = p
escape (later f) = escape (f x₀)
```

```
⫫-principled-naive : {xs : L} → ⫫-principled xs → ⫫-naive xs
-- Holify
⫫-principled-naive p = escape p
```

With the forcing extension's bottom at hand, we can define the
forcing extension's negation operation.

```
infix 3 ⫬_
⫬_ : (L → Set) → (L → Set)
⫬_ P = P ⇒ ⫫
```

The following observation is occassionally useful in order to
establish that certain double negations hold.

```
dense→negneg : {P : L → Set} → ((xs : L) → ∃[ ys ] P (xs ++ ys)) → (⫬ ⫬ P) []
-- Holify
dense→negneg h = λ xs q → q (fst (h xs)) (snd (h xs))
```


## Freshness of the generic sequence

Let us prove, up to a double negation, that the generic sequence differs from
any given sequence `ℕ → X` of the base universe in at least one term---assuming
that there is some fixpoint-free function `step : X → X`.

```
f₀-fresh
  : (step : X → X) (fixpoint-free : {x : X} → step x ≡ x → ⊥)
  → (g : ℕ → X)
  → (⫬ ⫬ (∇' (∃[ n ] (f₀[ n ]≡ step (g n))))) []
-- Holify
f₀-fresh step fixpoint-free g = dense→negneg {∇' (∃[ n ] (f₀[ n ]≡ step (g n)))} λ xs →
  step (g (length xs)) ∷ [] , now (length xs , lemma xs (step (g (length xs))))
  where
  lemma : (xs : L) (a : X) → lookupMaybe (xs ++ (a ∷ [])) (length xs) ≡ just a
  lemma []       a = refl
  lemma (x ∷ xs) a = lemma xs a
```

::: Hint :::
Use `dense→negneg`, and prove the following auxiliary lemma:
`(xs : L) (a : X) → lookupMaybe (xs ++ (a ∷ [])) (length xs) ≡ just a`
:::

<!--
```code
f₀-fresh'
  : (step : X → X) (fixpoint-free : {x : X} → step x ≡ x → ⊥)
  → (g : ℕ → X)
  → (⫬ withInstance ((n : ℕ) → f₀[ n ]≡ g n)) []
f₀-fresh' step fixpoint-free g xs p = f₀-fresh step fixpoint-free g xs λ ys q →
  --escape (q >>= λ (n , eq) → now (fixpoint-free (just-injective (trans (sym eq) {!p n!}))))
  where
  just-injective : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl
```
-->


## Genericity of the generic sequence

For a sequence `f : ℕ → X` and a number `n`, we define `f ↓ n` to be
the list of the first `n` values of `f`, i.e. the list `f zero ∷ f one
∷ … ∷ f (pred n) ∷ []`.

```
_↓_ : (ℕ → X) → ℕ → List X
f ↓ zero   = []
f ↓ succ n = (f ↓ n) ∷ʳ f n
```

```
generic⇒actual : {P : L → Set} → (f : ℕ → X) (n : ℕ) → ∇ P (f ↓ n) → ∃[ m ] P (f ↓ m)
-- Holify
generic⇒actual f n (now   p) = n , p
generic⇒actual f n (later k) = generic⇒actual f (succ n) (k (f n))
```

The following theorem can be read as follows: "If the generic sequence
in the forcing extension has property `P`, then so does (a suitable
finite prefix) of any actual sequence in the base universe."

```
generic⇒actual₀ : {P : L → Set} → (f : ℕ → X) → ∇ P [] → ∃[ m ] P (f ↓ m)
generic⇒actual₀ f = generic⇒actual f zero
```
