```
module Padova2025.ProgrammingBasics.Lists where
```

# Lists

In the Agda community, lists are usually written like `a ∷ b ∷ c ∷ []`, or more
precisely `a ∷ (b ∷ (c ∷ []))`. The symbol `[]` denotes the empty list. The
operator `_∷_` is used for appending ("consing") a single element in front of
an already existing tail of elements. The code to implement this syntax is the
following.

```
infixr 5 _∷_
data List (A : Set) : Set where  -- enter `∷` by `\::`
  []  : List A
  _∷_ : A → List A → List A
```

The variable `A` appearing in this datatype definition is a *parameter*. In
effect, for each type `A`, a new type `List A` is introduced. If Agda didn't
support parameters, we would be forced to repeat ourselves, for instance with
tedious code as the following.

```code
data ListOfBools : Set where
  []  : ListOfBools
  _∷_ : Bool → ListOfBools → ListOfBools

data ListOfNats : Set where
  []  : ListOfNats
  _∷_ : ℕ → ListOfNats → ListOfNats
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

The parameter `A` is here put in curly brackets so that when calling `length`,
it does not need to be explicitly mentioned: From the explicit argument, a
certain list, Agda is able to infer the type of its elements.


## Exercise: Concatenation

Define a binary operator which concatenates two lists. For instance,
`(a ∷ b ∷ []) ++ (c ∷ d ∷ [])` should reduce to `a ∷ b ∷ c ∷ d ∷ []`.

```
_++_ : {A : Set} → List A → List A → List A
-- Holify
_++_ []       ys = ys
_++_ (x ∷ xs) ys = x ∷ (xs ++ ys)

-- Tests
-- EX: (zero ∷ one ∷ []) ++ (two ∷ three ∷ []) ≡ (zero ∷ one ∷ two ∷ three ∷ [])
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


## Exercise: Snocking

For instance, `(a ∷ b ∷ c ∷ []) ∷ʳ z` should reduce to `a ∷ b ∷ c ∷ z`.

```
_∷ʳ_ : {A : Set} → List A → A → List A
-- Holify
_∷ʳ_ []       y = y ∷ []
_∷ʳ_ (x ∷ xs) y = x ∷ (xs ∷ʳ y)

-- Tests
-- EX: (zero ∷ one ∷ []) ∷ʳ two ≡ (zero ∷ one ∷ two ∷ [])
```


## Exercise: Reversal

Write a function which reverses the elements of a list. For instance, `reverse
(a ∷ b ∷ c ∷ [])` should reduce to `c ∷ b ∷ a ∷ []`.

```
reverse : {A : Set} → List A → List A
-- Holify
reverse []       = []
reverse (x ∷ xs) = reverse xs ∷ʳ x

-- Alternatively, in tail-recursive form thanks to an accumulator:
-- reverse = reverseAcc []
--   where
--   reverseAcc : {A : Set} → List A → List A → List A
--   reverseAcc acc []       = acc
--   reverseAcc acc (x ∷ xs) = reverseAcc (x ∷ acc) xs

-- Tests
-- EX: reverse (zero ∷ one ∷ two ∷ []) ≡ (two ∷ one ∷ zero ∷ [])
```


## Exercise: A higher-kinded function

The Agda expressions `List ℕ`, `List Bool` and so on denote certain types, i.e.
elements of `Set`. Is the bare expression `List`, without any argument, also
meaningful? What is its type?

```
List' : {--}Set → Set{--}
List' = List
```

::: Aside :::
In Haskell's two-level type system with types governing values and "kinds"
governing types, `List` would be called a "type constructor" of kind `* → *`.
:::
