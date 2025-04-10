```
module Padova2025.ProgrammingBasics.Lists where
```

# Lists

```
infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
```


## Exercise: Summing lists

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```

Define a function which sums the elements of a given list of natural numbers.

```
sum : List ℕ → ℕ
-- Holify
sum []       = zero
sum (x ∷ xs) = x + sum xs

-- Tests
-- EX: sum [] ≡ zero
-- EX: sum (one ∷ two ∷ three ∷ []) ≡ succ (succ (succ (succ (succ (succ zero)))))
```


## Exercise: Length of lists

Define a function which computes the length of a given list.

```
length : {A : Set} → List A → ℕ
-- Holify
length []       = zero
length (x ∷ xs) = succ (length xs)

-- Tests
-- EX: length (four ∷ []) ≡ one
-- EX: length (one ∷ two ∷ three ∷ []) ≡ three
```


## Exercise: Mapping over lists

Define the `map` function, which should apply the supplied function `f` to each
element in the input list.

For instance, `map f (x ∷ y ∷ z ∷ [])` should reduce to `f x ∷ f y ∷ f z ∷ []`.

```
map : {A B : Set} → (A → B) → List A → List B
-- Holify
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Tests
-- EX: map succ [] ≡ []
-- EX: map succ (one ∷ two ∷ []) ≡ two ∷ three ∷ []
```
