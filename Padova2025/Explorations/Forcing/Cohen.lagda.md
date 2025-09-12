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
open import Padova2025.ProvingBasics.Termination.Gas using (Maybe; nothing; just; lookupMaybe; just-injective)
open import Padova2025.ProvingBasics.Connectives.Existential
```

This module is parametrized by a set `X` which we assume to be inhabited by at
least one element `x₀`.
The purpose of this module is to provide suitable definitions so that
we can explore a forcing extension of the base universe in which a
*generic infinite sequence of elements of `X`* exists, i.e. a *generic
function `f₀ : ℕ → X`*. This function will turn out to be distinct from
every function `ℕ → X` of the base universe; hence Cohen forcing
allows us to enlarge the base universe by a new function `ℕ → X`
(without changing the naturals or the given type `X`).

This new function is *generic* in the sense that, for every property
`P` of a certain kind, if `f₀` has it, then so does every function
`f : ℕ → X` from the base universe (and indeed even every function `ℕ → X` in
any forcing extension).


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
  -- "P xs holds already now, no refinement required."
  now   : {xs : L} → P xs → ∇ P xs

  -- "P xs might not hold now, we need to wait at least for
  -- xs to grow by one element."
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

The generic sequence `f₀` exists a single entity only in the forcing extension.
To talk about it from the point of view of the base universe,
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


## Implication in the forcing extension

Let `P` and `Q` be two approximation-dependent propositions,
i.e. functions of type `L → Set`. What should it mean that `P`
implies `Q`?  More precisely, given an approximation `xs`, what should
it mean that `P` implies `Q` on stage `xs`?

One option would be given by the following straightforward definition,
which however we reject.

```
_⇒-naive_ : (L → Set) → (L → Set) → (L → Set)
P ⇒-naive Q = λ xs → (P xs → Q xs)
-- rejected proposal
```

This definition does not account for the possibility of `xs` evolving
to better approximations. The following actually adopted definition fixes this issue:

```
_⇒_ : (L → Set) → (L → Set) → (L → Set)
P ⇒ Q = λ xs → ((ys : L) → P (xs ++ ys) → Q (xs ++ ys))
```

Thorsten Altenkirch calls this style of definition *the logic of storytelling*:
Assume that, in a fantasy story, the wise wizard offers the counsel
"If our enemies cross that bridge, we will lose the war". This assertion does
not only mean that if the enemies cross the bridge now, the protagonists will
lose the war at that moment. It rather means that if at some point in the
future, after the story has continued, the enemies cross the bridge, the
protagonists will then lose the war.


## Negation in the forcing extension

Similarly, a principled definition of the forcing extension's bottom
proposition is *not*...

```
⫫-naive : L → Set
⫫-naive xs = ⊥
```

...but rather:

```
⫫-principled : L → Set
⫫-principled xs = ∇' ⊥ xs
-- fully spelled out: ⫫ xs = ∇ (λ ys → ⊥) xs
```

In other words, `⫫-principled xs` means that (eventually, after sufficiently
many refinements) `⊥` will hold. It is a positive way of expressing that the
given approximation `xs` is a dead end.

Fortunately, as we have assumed (in the very beginning of this file), that the type `X`
is inhabited (by some element `x₀`), the two definitions are actually equivalent,
and hence we will adopt the simpler one for the remaining development.

```
⫫ : L → Set
⫫ = ⫫-naive
```

Verifying that the principled definition indeed implies the naive one:

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

The following observation is occasionally useful in order to
establish that certain double negations hold.

```
dense→negneg : {P : L → Set} → ((xs : L) → ∃[ ys ] P (xs ++ ys)) → (⫬ ⫬ P) []
-- Holify
dense→negneg h = λ xs q → q (fst (h xs)) (snd (h xs))
```

::: More :::
In fact, a slightly more general result holds:

```
almostdense→negneg : {P : L → Set} → ((xs : L) → ¬ ¬ (∃[ ys ] P (xs ++ ys))) → (⫬ ⫬ P) []
-- Holify
almostdense→negneg h = λ xs q → h xs λ p → q (fst p) (snd p)
```

```
negneg→almostdense : {P : L → Set} → (⫬ ⫬ P) [] → ((xs : L) → ¬ ¬ (∃[ ys ] P (xs ++ ys)))
-- Holify
negneg→almostdense m xs f = m xs λ ys p → f (ys , p)
```
:::

This result (which, after a small modification is strengthened to an
equivalence in the folded subsection) suggests that dobule negation in
the forcing extension can be pronounced as *potentially*. The assertion
`(⫬ ⫬ P) []` means that it is *possible* for any given approximation
`xs` to evolve to a list which validates `P`, without presupposing
that no `P` will always hold eventually.


## Freshness of the generic sequence

Let us prove, up to a double negation, that the generic sequence differs from
any given sequence `ℕ → X` of the base universe in at least one term---assuming
that there is some fixpoint-free function `step : X → X`.

```
lemma-lookup-last : (xs : L) (a : X) → lookupMaybe (xs ++ (a ∷ [])) (length xs) ≡ just a
-- Holify
lemma-lookup-last []       a = refl
lemma-lookup-last (x ∷ xs) a = lemma-lookup-last xs a
```

```
f₀-fresh
  : (step : X → X) (fixpoint-free : {x : X} → step x ≡ x → ⊥)
  → (g : ℕ → X)
  → (⫬ ⫬ (∇' (∃[ n ] (f₀[ n ]≡ step (g n))))) []
-- Holify
f₀-fresh step fixpoint-free g = dense→negneg {∇' (∃[ n ] (f₀[ n ]≡ step (g n)))} λ xs →
  step (g (length xs)) ∷ [] , now (length xs , lemma-lookup-last xs (step (g (length xs))))
```

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


## Markov's principle

Markov's principle states: If a sequence `ℕ → ℕ` does *not not* have a zero,
then it actually has a zero. As an instance of the principle of double negation
elimination, Markov's principle is readily available in classical mathematics;
it is a taboo in most flavors of constructive mathematics. Specifically, in this
section we will explore that Markov's principle is falsified by the generic sequence.

Let us first prove that the generic sequence does *not not* have a certain value
`z` as one of its terms, as in the antecedent of Markov's principle. (The value `z` is a placeholder
for the natural number zero, which is an element of our fixed type `X` only in
case `X = ℕ`.)

```
generic-not-not-has-zero : (z : X) → (⫬ ⫬ (∇' (∃[ n ] f₀[ n ]≡ z))) []
-- Holify
generic-not-not-has-zero z = dense→negneg {(∇' (∃[ n ] f₀[ n ]≡ z))}
  λ xs → z ∷ [] , now (length xs , lemma-lookup-last xs z)
```

Contrary to what Markov's principle would predict, let us now also
prove that it is *not* the case that the generic sequence actually
attains the value `z`---assuming that there is some distinct value `w`
in `X`. This shows that Markov's principle is not valid for the
generic sequence.

```
↓-constant : (w : X) (n : ℕ) → (λ _ → w) ↓ n ≡ replicate n w
-- Holify
↓-constant w zero     = refl
↓-constant w (succ n) = trans (cong (_∷ʳ w) (↓-constant w n)) (sym (replicate-snoc n w))
```

```
not-generic-has-zero : (z w : X) → w ≢ z → ¬ (∇' (∃[ n ] f₀[ n ]≡ z) [])
not-generic-has-zero z w w≢z p with generic⇒actual₀ (λ _ → w) p
... | n , m , q = go n m {--}(trans (sym (cong (λ xs → lookupMaybe xs m) (↓-constant w n))) q){--}
  where
  go : (n m : ℕ) → lookupMaybe (replicate n w) m ≡ just z → ⊥
  go zero     m        = {--}λ (){--}
  go (succ n) zero     = {--}λ r → w≢z (just-injective r){--}
  go (succ n) (succ m) = {--}go n m{--}
```
