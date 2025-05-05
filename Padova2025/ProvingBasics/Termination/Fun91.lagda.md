```
module Padova2025.ProvingBasics.Termination.Fun91 where
```

# The 91 function

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.ProvingBasics.Termination.Gas
open import Padova2025.ProvingBasics.Connectives
```

```
{-# BUILTIN NATURAL ℕ #-}
```

Let us follow tradition and study the
[celebrated 91 function](https://en.wikipedia.org/wiki/McCarthy_91_function):

```code
f : ℕ → ℕ
f x with ≤-<-connex x 20
... | left  x≤20 = f (f (x + 11))
... | right x>20 = x ∸ 10
-- In the original, it is `100` instead of `20`.
-- We use the smaller value here to reduce load on the Let's play Agda server.
```

Because of the nested recursion, this definition presents a challenge
to termination analysis. This function is total, but this fact is not
obvious to Agda's termination checker---Agda rejects this definition
with the comment "Termination checking failed".


## Representing the function

To represent this function in Agda, we follow the same approach as in
the [previous module](Padova2025.ProvingBasics.Termination.Intricate0.html).

```
data Def : ℕ → Set
f₀ : (n : ℕ) → Def n → ℕ

data Def where
  gt20 : {n : ℕ} → n > 20 → Def n
  le20 : {n : ℕ} → n ≤ 20 → (p : Def (n + 11)) → Def (f₀ (n + 11) p) → Def n

f₀ n (gt20 _)     = n ∸ 10
f₀ n (le20 x p q) = f₀ (f₀ (n + 11) p) q
```


## Verifying totality

Clever ways have been proposed to prove the 91 function to be total.
Here we want to showcase a "brute force" method. For the inputs `0`
to `20` for which termination is not obvious, we blithely run the
recursion (with a gas limit in place) to observe, without any actual
insight to the function's behavior, that the recursion terminates.

```
observe-termination : (gas : ℕ) (n : ℕ) → Maybe (Def n)
observe-termination zero n = nothing
observe-termination (succ gas) n with ≤-<-connex n 20
... | right n>20 = just (gt20 n>20)
... | left n≤20  = do
  p ← observe-termination gas (n + 11)
  q ← observe-termination gas (f₀ (n + 11) p)
  just (le20 n≤20 p q)
```

```
collect : {P : ℕ → Set} → ((n : ℕ) → Maybe (P n)) → (n : ℕ) → Maybe (All P (downFrom n))
-- Holify
collect observe zero     = just []
collect observe (succ n) = do
  xs ← collect observe n
  p  ← observe n
  just (p ∷ xs)
```

```
empirical-fact : All Def (downFrom 21)
empirical-fact = from-just {--}(collect (observe-termination 15) 21){--}
```

With the difficult cases dealt with empirically, we are now in a
position to verify totality.

```
total : (n : ℕ) → Def n
total n with ≤-<-connex n 20
... | left  n≤20 = {--}lookup empirical-fact (succ-monotone n≤20){--}
... | right n>20 = {--}gt20 n>20{--}
```

With the totality proof in place, we can also define a manifestly
total version of the 91 function.

```
f : ℕ → ℕ
f n = f₀ n (total n)
```


## Determining the function values

It turns out that the 91 function has the same values as the following
non-recursively defined function.

```
g : ℕ → ℕ
g x = max 21 x ∸ 10
```

We want to prove agreement by using the brute force approach again.

```
observe-equality : (n : ℕ) → Maybe (f n ≡ g n)
observe-equality n with <-cmp (f n) (g n)
... | left  fn≡gn = just fn≡gn
... | right _     = nothing
```

```
empirical-fact' : All (λ(n : ℕ) → f n ≡ g n) (downFrom 21)
empirical-fact' = from-just {--}(collect observe-equality 21){--}
```

```
f≗g : (n : ℕ) → n ≤ 20 → f n ≡ g n
f≗g n n≤20 = lookup empirical-fact' (succ-monotone n≤20)
```
