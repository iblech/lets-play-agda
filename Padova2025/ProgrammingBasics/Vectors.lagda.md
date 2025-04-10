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

For instance, `dropV (succ zero) (a ∷ b ∷ c ∷ [])` should evaluate to `b ∷ c ∷ []`.

```
dropV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A n
-- Holify
dropV zero xs = xs
dropV (succ n) (x ∷ xs) = dropV n xs
```


## Exercise: take

For instance, `takeV (succ zero) (a ∷ b ∷ c ∷ [])` should evaluate to `a ∷ []`.

```
takeV : {A : Set} {n : ℕ} (k : ℕ) → Vector A (k + n) → Vector A k
-- Holify
takeV zero     xs       = []
takeV (succ n) (x ∷ xs) = x ∷ takeV n xs
```


## Exercise: Concatenation

For instance, `(a ∷ b ∷ []) ++ (c ∷ d ∷ [])` should evaluate to `a ∷ b ∷ c ∷ d ∷ []`.

```
_++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
-- Holify
_++_ []       ys = ys
_++_ (x ∷ xs) ys = x ∷ (xs ++ ys)
```

<!--

-- For instance, "snocV (a ∷ b ∷ []) c" should evaluate to "a ∷ b ∷ c ∷ []".
snocV : {A : Set} {n : ℕ} → Vector A n → A → Vector A (succ n)
snocV xs y = {!!}
-->
