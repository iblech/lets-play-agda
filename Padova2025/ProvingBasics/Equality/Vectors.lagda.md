```
module Padova2025.ProvingBasics.Equality.Vectors where
```

# Results on vectors

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Vectors
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```

## Take and drop

```
take-drop
  : {A : Set} {n : ℕ} (k : ℕ) (xs : Vector A (k + n))
  → takeV k xs ++V dropV k xs ≡ xs
-- Holify
take-drop zero     xs       = refl
take-drop (succ k) (x ∷ xs) = cong (x ∷_) (take-drop k xs)
```


## Associativity

Determine where the difficulty is in stating that `_++V_` is associative.

::: More :::
Let `xs : Vector A n`, `ys : Vector A m` and `zs : Vector A o`.

Then `(xs ++V ys) ++V zs` is of type `Vector A ((n + m) + o`, whereas `xs ++V (ys ++V zs)`
is of type `Vector A (n + (m + o))`.

These two types are equal, but not by definition. Hence the expression "`(xs
++V ys) ++V zs ≡ xs ++V (ys ++V zs)`" is ill-typed. To state the desired
equality, we have three options.

1. Transport one of the two sides of the equation to the type of the other.
2. Introduce so-called *heterogeneous equality*.
3. Switch to Cubical Agda, where we still have to do the transporting (and
   heterogeneous equality does no longer work well), but where working with
   this transporting gets simplified.

```
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```


### Method 1: Transporting one of the two sides of the equation

```
cons-subst
  : {A : Set} {n m : ℕ}
  → (p : n ≡ m) (x : A) (xs : Vector A n)
  → subst (Vector A) (cong succ p) (x ∷ xs) ≡ x ∷ subst (Vector A) p xs
-- Holify
cons-subst refl x xs = refl
```

```
++V-assoc
  : {A : Set} {n m o : ℕ} (xs : Vector A n) (ys : Vector A m) (zs : Vector A o)
  → subst (Vector A) (+-assoc n m o) ((xs ++V ys) ++V zs) ≡ xs ++V (ys ++V zs)
-- Holify
++V-assoc [] ys zs = refl
++V-assoc {n = succ n} (x ∷ xs) ys zs =
  trans (cons-subst (+-assoc n _ _) _ _) (cong (x ∷_) (++V-assoc xs ys zs))
```


### Method 1': Transporting one of the two sides, but with a twist

Method 1 becomes more pleasant by introducing a `cast` operation which, unlike
`subst`, does not look at the given equality witness, as in the
[standard library](https://agda.github.io/agda-stdlib/experimental/Data.Vec.Properties.html#++-assoc-eqFree).
It also becomes more pleasant when
[using Cubical Agda](https://agda.github.io/cubical/Cubical.Data.Vec.Properties.html#587).
In both variations, there is no longer a need for `cons-subst`.

The trick is to not pattern match on the equality witness, but only on the
dimensions and on the vectors themselves.

In the following type signature, the dot before `(n ≡ m)` expresses that we
will not look at the value of this argument (and Agda will then forbid us
from peeking).

```
cast
  : {A : Set} {n m : ℕ}
  → .(n ≡ m) → Vector A n → Vector A m
-- Holify
cast {m = zero}   p []       = []
cast {m = succ m} p (x ∷ xs) = x ∷ cast (succ-injective p) xs
```

```
cast-is-id
  : {A : Set} {n : ℕ}
  → (p : n ≡ n) (xs : Vector A n)
  → cast p xs ≡ xs
-- Holify
cast-is-id p []       = refl
cast-is-id p (x ∷ xs) = cong (x ∷_) (cast-is-id (succ-injective p) xs)
```

```
++V-assoc'
  : {A : Set} {n m o : ℕ} (xs : Vector A n) (ys : Vector A m) (zs : Vector A o)
  → cast (+-assoc n m o) ((xs ++V ys) ++V zs) ≡ xs ++V (ys ++V zs)
-- Holify
++V-assoc' []       ys zs = cast-is-id refl (ys ++V zs)
++V-assoc' (x ∷ xs) ys zs = cong (x ∷_) (++V-assoc' xs ys zs)
```


### Method 2: Heterogeneous equality

Alternatively, we can introduce so-called *heterogeneous equality*. However,
the `iconv` function presented below requires the
[K axiom](https://agda.readthedocs.io/en/latest/language/without-k.html)
which is incompatible with Cubical Agda. We hence only include this alternative
here as a comment.

```
infix 4 _≅_
data _≅_ {A : Set} (x : A) : {B : Set} → B → Set₁ where
   refl : x ≅ x
```

```
{-
icong
  : {I : Set} (F : I → Set) {G : {k : I} → F k → Set}
  → {i j : I} {x : F i} {y : F j}
  → i ≡ j → (f : {k : I} (z : F k) → G z)
  → x ≅ y
  → f x ≅ f y
icong F refl _ refl = refl

++V-assoc''
  : {A : Set} {n m o : ℕ} (xs : Vector A n) (ys : Vector A m) (zs : Vector A o)
  → (xs ++V ys) ++V zs ≅ xs ++V (ys ++V zs)
++V-assoc''              []       ys zs = refl
++V-assoc'' {n = succ n} (x ∷ xs) ys zs = icong (Vector _) (+-assoc n _ _) (x ∷_) (++V-assoc'' xs ys zs)
-}
```
:::
