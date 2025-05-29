```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Equality.Reasoning where
```

# Equational reasoning

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

The equality proofs we have discussed before have been put in so-called
*combinatorial style*, making use of the *combinators*
[`trans`](Padova2025.ProvingBasics.Equality.General.html#trans),
[`sym`](Padova2025.ProvingBasics.Equality.General.html#sym) and
and [`cong`](Padova2025.ProvingBasics.Equality.General.html#cong). While proofs
in this style are not too unreasonable to construct, if one makes extensive use
of Agda's assistive features, the resulting proofs are often hard to read. Such
"write-only" proofs constitute an antithesis to the ideals of elegance we are
striving for when playing Agda. They also look totally unlike usual blackboard
proofs of identities.

Instead, on a blackboard, we usually verify identities by chains of
equalities, using `trans` implicitly rather than explicitly. This style is
called *equational reasoning*, and it is also available in Agda. For instance,
here is how the [proof of commutativity of addition](Padova2025.ProvingBasics.Equality.NaturalNumbers.html#+-comm)
looks like in this style.

```
open import Padova2025.ProvingBasics.Equality.Reasoning.Core
-- not magic, but nevertheless recommended to skip on first reading

+-comm' : (a b : ℕ) → a + b ≡ b + a
+-comm' zero     b = sym (+-zero b)
+-comm' (succ a) b = begin
  succ a + b   ≡⟨⟩
  succ (a + b) ≡⟨ cong succ (+-comm' a b) ⟩
  succ (b + a) ≡⟨ sym (+-succ b a) ⟩
  b + succ a   ∎

-- compare with the combinator-style proof:
-- +-comm (succ a) b =
--   trans (cong succ (+-comm a b)) (sym (+-succ b a))
```

We start with the left-hand side and then repeatedly carry out manipulations
until we arrive at the right-hand side. Steps indicated by `≡⟨⟩` hold by
definition (by [`refl`](Padova2025.ProvingBasics.Equality.Base.html#_≡_.refl)).
Steps indicated by `≡⟨ p ⟩` hold by the specified reason (element of the
corresponding identity type) `p`.

::: Aside :::
Instead of `≡⟨ sym p ⟩`, we can also write `≡˘⟨ p ⟩`.
:::


## Exercise: Distributivity, revisited

Redo the [earlier proof](Padova2025.ProvingBasics.Equality.NaturalNumbers.html#·-distribʳ-+)
of distributivity in equational style.

```
·-distribʳ-+' : (a b c : ℕ) → (a + b) · c ≡ a · c + b · c
-- Holify
·-distribʳ-+' zero     b c = refl
·-distribʳ-+' (succ a) b c = begin
  (succ a + b) · c    ≡⟨⟩
  succ (a + b) · c    ≡⟨⟩
  c + (a + b) · c     ≡⟨ cong (c +_) (·-distribʳ-+' a b c) ⟩
  c + (a · c + b · c) ≡˘⟨ +-assoc c (a · c) (b · c) ⟩
  (c + a · c) + b · c ≡⟨⟩
  succ a · c  + b · c ∎
```


## Exercise: Commutativity of multiplication

```
·-zero : (a : ℕ) → a · zero ≡ zero
-- Holify
·-zero zero     = refl
·-zero (succ a) = ·-zero a
```

```
+-swap : (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
-- Holify
+-swap a b c = begin
  a + (b + c) ≡˘⟨ +-assoc a b c ⟩
  (a + b) + c ≡⟨ cong (_+ c) (+-comm a b) ⟩
  (b + a) + c ≡⟨ +-assoc b a c ⟩
  b + (a + c) ∎
```

```
·-succ : (a b : ℕ) → a · succ b ≡ a + a · b
-- Holify
·-succ zero     b = refl
·-succ (succ a) b = begin
  succ a · succ b        ≡⟨⟩
  succ b + a · succ b    ≡⟨ cong (succ b +_) (·-succ a b) ⟩
  succ b + (a + a · b)   ≡⟨ +-swap (succ b) a (a · b) ⟩
  a + (succ b + a · b)   ≡⟨⟩
  a + succ (b + a · b)   ≡⟨ +-succ a (b + a · b) ⟩
  succ (a + (b + a · b)) ≡⟨⟩
  succ a + succ a · b    ∎
```

```
·-comm : (a b : ℕ) → a · b ≡ b · a
-- Holify
·-comm zero     b = sym (·-zero b)
·-comm (succ a) b = begin
  succ a · b ≡⟨⟩
  b + a · b  ≡⟨ cong (b +_) (·-comm a b) ⟩
  b + b · a  ≡˘⟨ ·-succ b a ⟩
  b · succ a ∎
```

As a corollary, from commutativity and the [first distributive
law](Padova2025.ProvingBasics.Equality.NaturalNumbers.html#·-distribʳ-+) we obtain the other distributive law.

```
·-distribˡ-+ : (a b c : ℕ) → a · (b + c) ≡ a · b + a · c
-- Holify
·-distribˡ-+ a b c = begin
  a · (b + c)   ≡⟨ ·-comm a (b + c) ⟩
  (b + c) · a   ≡⟨ ·-distribʳ-+ b c a ⟩
  b · a + c · a ≡⟨ cong₂ _+_ (·-comm b a) (·-comm c a) ⟩
  a · b + a · c ∎
```


## Exercise: Binomial theorem

```
binomial-theorem : (x y : ℕ) → (x + y) ² ≡ x ² + two · (x · y) + y ²
-- Holify
binomial-theorem x y = begin
  (x + y) ²                         ≡⟨⟩
  (x + y) · (x + y)                 ≡⟨ ·-distribʳ-+ x y (x + y) ⟩
  x · (x + y) + y · (x + y)         ≡⟨ cong₂ (_+_) (·-distribˡ-+ x x y) (·-distribˡ-+ y x y) ⟩
  (x · x + x · y) + (y · x + y · y) ≡⟨ +-assoc (x · x) (x · y) (y · x + y · y) ⟩
  x ² + (x · y + (y · x + y ²))     ≡˘⟨ cong (x ² +_) (+-assoc (x · y) (y · x) (y ²)) ⟩
  x ² + ((x · y + y · x) + y ²)     ≡⟨ cong (λ a → x ² + (a + y ²)) lemma ⟩
  x ² + (two · (x · y) + y ²)       ≡˘⟨ +-assoc (x ²) (two · (x · y)) (y ²) ⟩
  x ² + two · (x · y) + y ²         ∎
  where
  lemma : x · y + y · x ≡ two · (x · y)
  lemma = trans (cong ((x · y) +_) (·-comm y x)) (two-+-+ (x · y))
```

It is instructive to do this proof, once, by hand, so as to appreciate the
nontriviality of the binomial theorem if the only tools available are
the axioms and their basic consequences. There is a
[ring solver](https://gist.github.com/andrejbauer/358722620c26c09d6be218bcd95ee654)
which can generate the proof automatically.


## Exercise: Summing with and without an accumulator

```
open import Padova2025.ProgrammingBasics.Lists
```

[Back when we have introduced lists](Padova2025.ProgrammingBasics.Lists.html#sum),
we have implemented a `sum` function which sums the elements of a
given list of natural numbers:

```
-- sum : List ℕ → ℕ
-- sum []       = zero
-- sum (x ∷ xs) = x + sum xs
```

An alternative, tail-recursive, implementation makes use of an accumulator:

```
sumAcc : ℕ → List ℕ → ℕ
sumAcc acc []       = acc
sumAcc acc (x ∷ xs) = sumAcc (acc + x) xs

sum' : List ℕ → ℕ
sum' = sumAcc zero
```

Let us prove that these two implementations yield identical results.

```
lemma-sumAcc : (acc : ℕ) (xs : List ℕ) → sumAcc acc xs ≡ acc + sum xs
-- Holify
lemma-sumAcc acc []       = sym (+-zero acc)
lemma-sumAcc acc (x ∷ xs) = begin
  sumAcc acc (x ∷ xs) ≡⟨⟩
  sumAcc (acc + x) xs ≡⟨ lemma-sumAcc (acc + x) xs ⟩
  (acc + x) + sum xs  ≡⟨ +-assoc acc x (sum xs) ⟩
  acc + (x + sum xs)  ∎
```

```
sum-sum' : (xs : List ℕ) → sum xs ≡ sum' xs
-- Holify
sum-sum' xs = sym (lemma-sumAcc zero xs)
```


## Exercise: Reversing with and without an accumulator

Similarly to the previous exercise---there are two natural
implementations of the `reverse` function on lists, not using or using
an accumulator:

```
-- Without accumulator.
-- reverse : {A : Set} → List A → List A
-- reverse []       = []
-- reverse (x ∷ xs) = reverse xs ∷ʳ x

-- With accumulator.
reverseAcc : {A : Set} → List A → List A → List A
reverseAcc acc []       = acc
reverseAcc acc (x ∷ xs) = reverseAcc (x ∷ acc) xs

reverse' : {A : Set} → List A → List A
reverse' = reverseAcc []
```

For the following proof, the function [snoc-++](Padova2025.ProvingBasics.Equality.Lists.html#snoc-++) is useful.

```
open import Padova2025.ProvingBasics.Equality.Lists
```

```
lemma-reverseAcc : {A : Set} (acc : List A) (xs : List A) → reverseAcc acc xs ≡ reverse xs ++ acc
-- Holify
lemma-reverseAcc acc [] = refl
lemma-reverseAcc acc (x ∷ xs) = begin
  reverseAcc acc (x ∷ xs)  ≡⟨⟩
  reverseAcc (x ∷ acc) xs  ≡⟨ lemma-reverseAcc (x ∷ acc) xs ⟩
  reverse xs ++ (x ∷ acc)  ≡˘⟨ snoc-++ x (reverse xs) acc ⟩
  (reverse xs ∷ʳ x) ++ acc ≡⟨⟩
  reverse (x ∷ xs) ++ acc  ∎
```

```
reverse-reverse' : {A : Set} (xs : List A) → reverse xs ≡ reverse' xs
-- Holify
reverse-reverse' xs = sym (trans (lemma-reverseAcc [] xs) (++-[] (reverse xs)))
```
