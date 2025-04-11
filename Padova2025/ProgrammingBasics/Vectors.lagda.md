```
module Padova2025.ProgrammingBasics.Vectors where
```

# Vectors

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```

```
infixr 5 _∷_
data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)
```


## Exercise: Length

Define a function which computes the length of a given vector.
There are two possible implementations, one which runs in constant time
and one which runs in linear time.

```
lengthV : {n : ℕ} {A : Set} → Vector A n → ℕ
-- Holify
lengthV {n} xs = n
```


## Exercise: Map

Define the `map` function for vectors.
For instance, `map f (x ∷ y ∷ z ∷ [])` should reduce to `f x ∷ f y ∷ f z ∷ []`.

```
mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
-- Holify
mapV f [] = []
mapV f (x ∷ xs) = f x ∷ mapV f xs
```


## Exercise: zipWith

For instance, "zipWithV f (x ∷ y ∷ []) (a ∷ b ∷ [])" should evaluate to "f x a ∷ f y b ∷ []".

```
zipWithV : {A B C : Set} {n : ℕ} → (A → B → C) → Vector A n → Vector B n → Vector C n
-- Holify
zipWithV f [] [] = []
zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys
```


## Exercise: drop

For instance, `dropV one (a ∷ b ∷ c ∷ [])` should evaluate to `b ∷ c ∷ []`.

```
dropV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
-- Holify
dropV zero xs = xs
dropV (succ n) (x ∷ xs) = dropV n xs

-- Tests
-- EX: dropV one (zero ∷ one ∷ two ∷ []) ≡ (one ∷ two ∷ [])
```


## Exercise: take

For instance, `takeV one (a ∷ b ∷ c ∷ [])` should evaluate to `a ∷ []`.

```
takeV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
-- Holify
takeV zero     xs       = []
takeV (succ n) (x ∷ xs) = x ∷ takeV n xs

-- Tests
-- EX: takeV one (zero ∷ one ∷ two ∷ []) ≡ (zero ∷ [])
```


## Exercise: Concatenation

For instance, `(a ∷ b ∷ []) ++V (c ∷ d ∷ [])` should evaluate to `a ∷ b ∷ c ∷ d ∷ []`.

```
_++V_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
-- Holify
_++V_ []       ys = ys
_++V_ (x ∷ xs) ys = x ∷ (xs ++V ys)

-- Tests
-- EX: (zero ∷ one ∷ []) ++V (two ∷ three ∷ []) ≡ (zero ∷ one ∷ two ∷ three ∷ [])
```


## Exercise: Snocking

Write a function which appends a new element at the end.
For instance, `snocV (a ∷ b ∷ []) c` should evaluate to `a ∷ b ∷ c ∷ []`.

```
snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
-- Holify
snocV []       y = y ∷ []
snocV (x ∷ xs) y = x ∷ snocV xs y

-- Tests
-- EX: snocV (zero ∷ one ∷ []) two ≡ (zero ∷ one ∷ two ∷ [])
```


## Exercise: Reversal

For instance, `reverseV (a ∷ b ∷ c ∷ [])` should evaluate to `c ∷ b ∷ a ∷ []`.

```
reverseV : {A : Set} {n : ℕ} → Vector A n → Vector A n
-- Holify
reverseV []       = []
reverseV (x ∷ xs) = snocV (reverseV xs) x

-- Tests
-- EX: reverseV (zero ∷ one ∷ two ∷ []) ≡ (two ∷ one ∷ zero ∷ [])
```


## Exercise: Flattening vectors of vectors

For instance, `concatV ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])` should evaluate
to `a ∷ b ∷ c ∷ d ∷ []`.

```
concatV : {--}{A : Set} {n m : ℕ} → Vector (Vector A n) m → Vector A (m · n){--}
-- Holify
concatV []         = []
concatV (xs ∷ xss) = xs ++V concatV xss

-- Tests
-- EX: concatV ((zero ∷ one ∷ []) ∷ (two ∷ four ∷ []) ∷ []) ≡ (zero ∷ one ∷ two ∷ four ∷ [])
```

::: Aside :::
Note that this exercise nontrivially depends on the somewhat arbitrary choices
in implementing addition and multiplication of natural numbers: Should the case
split be on the first or on the second argument? Should `succ a · b` be defined
as `b + a · b` or as `a · b + b`? Et cetera. This state of affairs is
unsatisfying and there are a couple of proposals attacking this problem. One of
these is [objective type theory](https://arxiv.org/abs/2102.00905) by Benno van
den Bergh and Martijn den Besten.
:::
