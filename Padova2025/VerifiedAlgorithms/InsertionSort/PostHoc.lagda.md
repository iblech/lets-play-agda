```
{-# OPTIONS --cubical-compatible #-}
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Connectives.Disjunction

module Padova2025.VerifiedAlgorithms.InsertionSort.PostHoc
  (A : Set) (_≤_ : A → A → Set) (cmp? : (x y : A) → x ≤ y ⊎ y ≤ x) where
```

# Post-hoc verification

```
open import Padova2025.VerifiedAlgorithms.InsertionSort.Implementation A _≤_ cmp?
```


## Output lists are ordered

As a first step, let us prove that the lists produced by the `sort`
function are always ascendingly ordered.  To express such an
assertion, we need to introduce a type `IsOrdered xs` of witnesses
that a given list `xs` is ordered.

```
data IsOrdered : List A → Set where
  empty     : IsOrdered []
  singleton : {x : A} → IsOrdered (x ∷ [])
  cons      : {x y : A} {ys : List A} → x ≤ y → IsOrdered (y ∷ ys) → IsOrdered (x ∷ (y ∷ ys))
```

```
lemma₀ : (x y : A) (ys : List A) → y ≤ x → IsOrdered (y ∷ ys) → IsOrdered (y ∷ insert x ys)
-- Holify
lemma₀ x y []       y≤x p = cons y≤x singleton
lemma₀ x y (z ∷ ys) y≤x (cons y≤z q) with cmp? x z
... | left  x≤z = cons y≤x (cons x≤z q)
... | right z≤x = cons y≤z (lemma₀ x z ys z≤x q)
```

```
lemma : (x : A) (ys : List A) → IsOrdered ys → IsOrdered (insert x ys)
-- Holify
lemma x []       p = singleton
lemma x (y ∷ ys) p with cmp? x y
... | left  x≤y = cons x≤y p
... | right y≤x = lemma₀ x y ys y≤x p
```

```
theorem : (xs : List A) → IsOrdered (sort xs)
-- Holify
theorem []       = empty
theorem (x ∷ xs) = lemma x (sort xs) (theorem xs)
```


## Output lists are permutations of the input lists

It is nice that a full proof of `theorem : (xs : List A) → IsOrdered
(sort xs)`, developed above, is just one screenful of code. However,
this theorem does not yet express all aspects of the sorting function
working correctly:

```
cheatsort : List A → List A
cheatsort xs = []
```

```
cheattheorem : (xs : List A) → IsOrdered (cheatsort xs)
cheattheorem xs = empty
```

We need to verify that `sort xs` is a permutation of the input list
`xs`. To express such an assertion, we first set up a type `x ◂ ys ↝
xys` of witnesses that inserting `x` into `ys` somewhere yields the
list `xys`.

```
data _◂_↝_ : A → List A → List A → Set where
  here  : {x : A} {xs : List A} → x ◂ xs ↝ (x ∷ xs)
  there : {x y : A} {ys xys : List A} → x ◂ ys ↝ xys → x ◂ (y ∷ ys) ↝ (y ∷ xys)
```

We then set up a type `xs ≈ ys` of witnesses that the two lists `xs` and `ys`
are permutations of each other, that is, contain exactly the same elements just
perhaps in different order.

```
infix 4 _≈_
data _≈_ : List A → List A → Set where
  empty : [] ≈ []
  cons  : {x : A} {xs ys xys : List A} → (x ◂ ys ↝ xys) → xs ≈ ys → (x ∷ xs) ≈ xys
```

Here is an example for such a permutation witness:

```
example : (x y z : A) → (x ∷ y ∷ z ∷ []) ≈ (z ∷ x ∷ y ∷ [])
-- Holify
example x y z = cons (there here) (cons (there here) (cons here empty))
```

We can then state and prove the fundamental lemma about the inserting
behavior of `insert`.

```
lemma' : (x : A) (ys : List A) → x ◂ ys ↝ insert x ys
-- Holify
lemma' x []       = here
lemma' x (y ∷ ys) with cmp? x y
... | left  x≤y = here
... | right y≤x = there (lemma' x ys)
```

The desired result about the `sort` function is then a quick corollary.

```
theorem' : (xs : List A) → xs ≈ sort xs
-- Holify
theorem' []       = empty
theorem' (x ∷ xs) = cons (lemma' x (sort xs)) (theorem' xs)
```
