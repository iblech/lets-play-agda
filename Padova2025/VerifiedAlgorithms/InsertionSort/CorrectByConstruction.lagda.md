```
{-# OPTIONS --cubical-compatible #-}
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Connectives.Disjunction

module Padova2025.VerifiedAlgorithms.InsertionSort.CorrectByConstruction
  (A : Set) (_≤_ : A → A → Set) (-∞ : A) (min! : {x : A} → -∞ ≤ x) (cmp? : (x y : A) → x ≤ y ⊎ y ≤ x) where
```

# Correct by construction

## Ordered output lists

Let us introduce the type `OList l` of ascendingly ordered lists where all elements are `≥ l`.
In other words, `OList l` is the type of ordered lists bounded from below by `l`.

```
data OList (l : A) : Set where
  nil  : OList l
  cons : (x : A) → l ≤ x → OList x → OList l
```

```
insert : {l : A} → (x : A) → l ≤ x → OList l → OList l
-- Holify
insert x l≤x nil             = cons x l≤x nil
insert x l≤x (cons y l≤y ys) with cmp? x y
... | left  x≤y = cons x l≤x (cons y x≤y ys)
... | right y≤x = cons y l≤y (insert x y≤x ys)
```

```
sort : List A → OList -∞
-- Holify
sort []       = nil
sort (x ∷ xs) = insert x min! (sort xs)
```

::: Aside :::
An alternative definition of ordered lists is as follows.

```
open import Padova2025.ProvingBasics.Termination.Gas using (𝟙; tt)

data OList₁ : Set
_≤head_ : A → OList₁ → Set

data OList₁ where
  nil  : OList₁
  cons : (x : A) (xs : OList₁) → x ≤head xs → OList₁

x ≤head nil         = 𝟙
x ≤head cons y ys _ = x ≤ y
```

However, working with this alternative definition is a bit more cumbersome than with `OList`.

::: Todo :::
Expand.
:::

<!--
insert₁ : A → OList₁ → OList₁
insert₁ x nil = cons x nil tt
insert₁ x ys@(cons y ys' y≤head-ys) with cmp? x y
... | left  x≤y = cons x ys x≤y
... | right y≤x = cons y (insert₁ x ys') {!!}
-->
:::


## Ordered and permuted output lists

As in the module on post-hoc verification, let us now also ensure in a
correct-by-construction way that the output list produced by insertion
sort is a permutation of the input list.

The following type declaration is [as in the module on post-hoc
verification](Padova2025.VerifiedAlgorithms.InsertionSort.PostHoc.html).

```
data _◂_↝_ : A → List A → List A → Set where
  here  : {x : A} {xs : List A} → x ◂ xs ↝ (x ∷ xs)
  there : {x y : A} {ys xys : List A} → x ◂ ys ↝ xys → x ◂ (y ∷ ys) ↝ (y ∷ xys)
```

The type `OPList l xs` is the type of ordered lists whose elements are
bounded from below by `l` and which are permutations of `xs`.
  
```
data OPList (l : A) : List A → Set where
  nil  : OPList l []
  cons : {ys xys : List A} → (x : A) → OPList x ys → l ≤ x → (x ◂ ys ↝ xys) → OPList l xys
```

As the outputs are now sufficiently constrained by the types, Agda's
automatic proof search `C-c C-a` will be able to correctly fill in several
key terms in the following two definitions.

```
insert' : {l : A} {ys : List A} → (x : A) → OPList l ys → l ≤ x → OPList l (x ∷ ys)
-- Holify
insert' x nil               l≤x = cons x nil l≤x here
insert' x (cons y ys l≤y p) l≤x with cmp? x y
... | left  x≤y = cons x (cons y ys x≤y p)  l≤x here
... | right y≤x = cons y (insert' x ys y≤x) l≤y (there p)
```

```
sort' : (xs : List A) → OPList -∞ xs
-- Holify
sort' []       = nil
sort' (x ∷ xs) = insert' x (sort' xs) min!
```

::: Todo :::
Comment on the requirement of `-∞`.
:::
