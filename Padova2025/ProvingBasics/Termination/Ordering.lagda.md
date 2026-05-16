```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Termination.Ordering where
```

# The standard ordering on the natural numbers

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

In this module, we introduce the standard ordering `_≤_` on the
natural numbers, together with its variants `_<_`, `_≥_` and `_>_`,
and verify their basic properties.

```
infix 4 _≤_ _<_ _≥_ _>_
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}   → zero ≤ n
  s≤s : {n m : ℕ} → (n≤m : n ≤ m) → succ n ≤ succ m

_<_ : ℕ → ℕ → Set
n < m = succ n ≤ m

_>_ : ℕ → ℕ → Set
n > m = m < n

_≥_ : ℕ → ℕ → Set
n ≥ m = m ≤ n
```


## Exercise: Reflexivity, transitivity and antisymmetry

```
≤-refl : {a : ℕ} → a ≤ a
-- Holify
≤-refl {zero}   = z≤n
≤-refl {succ a} = s≤s ≤-refl
```

```
≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
-- Holify
≤-trans z≤n     q       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
```

```
≤-antisymm : {a b : ℕ} → a ≤ b → b ≤ a → a ≡ b
-- Holify
≤-antisymm z≤n     z≤n     = refl
≤-antisymm (s≤s p) (s≤s q) = cong succ (≤-antisymm p q)
```

```
<-irreflexive : {a : ℕ} → a < a → ⊥
-- Holify
<-irreflexive (s≤s p) = <-irreflexive p
```

```
<-irreflexive' : {a b : ℕ} → a ≤ b → b < a → ⊥
-- Holify
<-irreflexive' (s≤s p) (s≤s q) = <-irreflexive' p q
```

```
≡⇒≤ : {a b : ℕ} → a ≡ b → a ≤ b
-- Holify
≡⇒≤ refl = ≤-refl
```


## Exercise: Decision procedures

```
≤-<-connex : (a b : ℕ) → a ≤ b ⊎ b < a
-- Holify
≤-<-connex zero     b        = left z≤n
≤-<-connex (succ a) zero     = right (s≤s z≤n)
≤-<-connex (succ a) (succ b) with ≤-<-connex a b
... | left  a≤b = left  (s≤s a≤b)
... | right b<a = right (s≤s b<a)
```

::: Hint :::
Perhaps surprisingly, this exercise and the next exercise can both be
solved on autopilot. Judiciously use `C-c C-c`, `C-c C-a` and the
`with` keyword to pattern match on the result of a suitable recursive
call.
:::

```
<-cmp : (a b : ℕ) → a ≡ b ⊎ (a < b ⊎ a > b)
-- Holify
<-cmp zero     zero     = left refl
<-cmp zero     (succ b) = right (left (s≤s z≤n))
<-cmp (succ a) zero     = right (right (s≤s z≤n))
<-cmp (succ a) (succ b) with <-cmp a b
... | left  a≡b         = left (cong succ a≡b)
... | right (left a<b)  = right (left (s≤s a<b))
... | right (right a>b) = right (right (s≤s a>b))
```


## Exercise: Ordering properties of several functions

```
succ-monotone : {a b : ℕ} → a ≤ b → succ a ≤ succ b
succ-monotone = s≤s
```

```
pred-monotone : {a b : ℕ} → a ≤ b → pred a ≤ pred b
-- Holify
pred-monotone z≤n     = z≤n
pred-monotone (s≤s p) = p
```

```
succ-inflationary : (a : ℕ) → a ≤ succ a
-- Holify
succ-inflationary zero     = z≤n
succ-inflationary (succ a) = s≤s (succ-inflationary a)
```

```
twice-inflationary : (a : ℕ) → a ≤ twice a
-- Holify
twice-inflationary zero     = z≤n
twice-inflationary (succ a) = ≤-trans (succ-inflationary (succ a)) (succ-monotone (succ-monotone (twice-inflationary a)))
```

```
max-inflationaryₗ : (a b : ℕ) → a ≤ max a b
-- Holify
max-inflationaryₗ zero     b        = z≤n
max-inflationaryₗ (succ a) zero     = ≤-refl
max-inflationaryₗ (succ a) (succ b) = s≤s (max-inflationaryₗ a b)
```

```
max-inflationaryᵣ : (a b : ℕ) → b ≤ max a b
-- Holify
max-inflationaryᵣ zero     b        = ≤-refl
max-inflationaryᵣ (succ a) zero     = z≤n
max-inflationaryᵣ (succ a) (succ b) = s≤s (max-inflationaryᵣ a b)
```

```
+-monotone : {a a' b b' : ℕ} → a ≤ b → a' ≤ b' → a + a' ≤ b + b'
-- Holify
+-monotone z≤n     z≤n     = z≤n
+-monotone z≤n     (s≤s q) = ≤-trans (succ-monotone (+-monotone z≤n q)) (≡⇒≤ (sym (+-succ _ _)))
+-monotone (s≤s p) q       = succ-monotone (+-monotone p q)
```

```
+-inflationaryₗ : (a b : ℕ) → a ≤ a + b
-- Holify
+-inflationaryₗ zero     b = z≤n
+-inflationaryₗ (succ a) b = s≤s (+-inflationaryₗ a b)
```

```
+-inflationaryᵣ : (a b : ℕ) → b ≤ a + b
-- Holify
+-inflationaryᵣ a b = +-monotone {zero} {b} {a} {b} z≤n ≤-refl
```


## Exercise: Maximum of a list

```
maximum : List ℕ → ℕ
maximum []       = zero
maximum (x ∷ xs) = max x (maximum xs)

maximum-≥ : (k : ℕ) (xs : List ℕ) → k ∈ xs → k ≤ maximum xs
maximum-≥ k (x ∷ xs) (here  refl) = max-inflationaryₗ x (maximum xs)
maximum-≥ k (x ∷ xs) (there p)    = ≤-trans (maximum-≥ k xs p) (max-inflationaryᵣ x (maximum xs))
```


## Exercise: Halving

```
half-≤ : (x : ℕ) → half x ≤ x
-- Holify
half-≤ zero            = z≤n
half-≤ (succ zero)     = z≤n
half-≤ (succ (succ x)) = succ-monotone (≤-trans (half-≤ x) (succ-inflationary x))
```

```
half-< : (x : ℕ) → half (succ x) < succ x
-- Holify
half-< zero     = s≤s z≤n
half-< (succ x) = succ-monotone (succ-monotone (half-≤ x))
```


## Exercise: Subtraction decreases

```
open import Padova2025.ProvingBasics.EvenOdd
```

```
monus-≤ : (a b : ℕ) → a ≥ b → a ∸ b ≤ a
-- Holify
monus-≤ a        zero     z≤n       = ≤-refl
monus-≤ (succ a) (succ b) (s≤s a≥b) = ≤-trans (monus-≤ a b a≥b) (succ-inflationary a)
```

```
monus-< : (a b : ℕ) → IsPositive b → a ≥ b → a ∸ b < a
-- Holify
monus-< (succ a) (succ zero)     b≥0  (s≤s a≥b) = ≤-refl
monus-< (succ a) (succ (succ b)) b≥-1 (s≤s a>b) =
  ≤-trans (monus-< a (succ b) (case-succ b) a>b) (succ-inflationary a)
```


## Infinitude of the even numbers

```
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.EvenOdd
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

A particularly positive way of expressing that there are infinitely
many even numbers is as follows: Beyond every natural number, there is
an even natural number. Let us state and prove this fact in Agda.

```
Even-infinite : (x : ℕ) → ∃[ y ] (y ≥ x × Even y)
-- Holify
Even-infinite x = twice x , twice-inflationary x , twice-even x
-- Alternatively, more economically, providing `x` or `succ x` instead
-- of `twice x` as witness:
-- Even-infinite x with even-or-odd x
-- ... | left  xeven = x      , ≤-refl              , xeven
-- ... | right xodd  = succ x , succ-inflationary x , succ-odd xodd
```


## Infinitude of the natural numbers

```
open import Padova2025.ProvingBasics.Connectives.Existential
```

One among several ways to express that there are infinitely many
natural numbers is as follows: For every finite list of natural
numbers, there is a natural number not in that list. We can formalize
and prove this assertion as follows.

```
ℕ-infinite : (xs : List ℕ) → ∃[ x ] x ∉ xs
ℕ-infinite xs = succ (sum xs) , λ p → <-irreflexive (go p)
  where
  go : {xs : List ℕ} {y : ℕ} → y ∈ xs → y < succ (sum xs)
  go (here  refl) = {--}succ-monotone (≤-trans (≡⇒≤ (sym (+-zero _))) (+-monotone ≤-refl z≤n)){--}
  go (there p)    = {--}≤-trans (go p) (succ-monotone (+-monotone z≤n ≤-refl)){--}
```


## Exercise: An alternative definition of the strict ordering relation

Occasionally the following alternative definition of the strict
less-than relation is useful.

```
data _<'_ : ℕ → ℕ → Set where
  base' : {n : ℕ}     → n <' succ n
  step' : {a b : ℕ}   → a <' b → a <' succ b
```

```
z<'s : {x : ℕ} → zero <' succ x
-- Holify
z<'s {zero}   = base'
z<'s {succ x} = step' z<'s
```

```
s<'s : {x y : ℕ} → x <' y → succ x <' succ y
-- Holify
s<'s base'     = base'
s<'s (step' p) = step' (s<'s p)
```

```
<⇒<' : {x y : ℕ} → x < y → x <' y
-- Holify
<⇒<' (s≤s p) = lemma p
  where
  lemma : {x y : ℕ} → x ≤ y → x <' succ y
  lemma z≤n     = z<'s
  lemma (s≤s p) = s<'s (lemma p)
```

```
<'⇒< : {x y : ℕ} → x <' y → x < y
-- Holify
<'⇒< base'     = ≤-refl
<'⇒< (step' p) = ≤-trans (<'⇒< p) (succ-inflationary _)
```


## Exercise: Indexing

```
lookup : {P : ℕ → Set} {n m : ℕ} → All P (downFrom n) → m < n → P m
-- Holify
lookup {P} {succ n} {m} (p ∷ ps) m<n with ≤-<-connex n m
... | left  n≤m = subst P (≤-antisymm n≤m (pred-monotone m<n)) p
... | right m<n = lookup ps m<n
```
