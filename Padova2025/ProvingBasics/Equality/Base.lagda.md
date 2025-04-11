```
module Padova2025.ProvingBasics.Equality.Base where
```

# Definition

```
infix 5 _≡_
data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a
```

```
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl
```


## Exercise: Transitivity

Fill in this hole, thereby proving that equality is transitive.

```
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- Holify
trans refl q = q
```


## Exercise: Pointwise equality

Prove that equal functions have equal values.
(The converse is a principle known as "function extensionality" which
can be postulated in Agda but is not assumed by default.)

```
equal→pwequal : {A B : Set} {f g : A → B} {x : A} → f ≡ g → f x ≡ g x
-- Holify
equal→pwequal refl = refl
```

## Exercise: Identity of indiscernibles

Identical values have all their properties in common: If `F : A → Set` is a
property of elements of a type `A` (for instance, `F` might be [the predicate `Even` from
before](Padova2025.ProvingBasics.EvenOdd.html#Even)) and if `x` and `y` are
identical elements, then `F x` should imply `F y`.

```
transport : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
-- Holify
transport F refl s = s
```

<!--
-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?
-->


## Exercise: Predecessor of successor

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```

Prove that the predecessor of a successor of a number is the original number
again.

```
lemma-pred-succ : (a : ℕ) → pred (succ a) ≡ a
lemma-pred-succ a = {--}refl{--}
```


## Exercise: One not zero

```
open import Padova2025.ProvingBasics.Negation
```

```
one≠zero : ¬ (one ≡ zero)
-- Holify
one≠zero ()
```

As a corollary, prove that it is not the case that for all numbers `a`, `succ
(pred a)` is the same as `a`:

```
lemma-succ-pred : ((a : ℕ) → succ (pred a) ≡ a) → ⊥
lemma-succ-pred f = {--}one≠zero (f zero){--}
```

Instead, the equation $\mathrm{succ}(\mathrm{pred}(a)) = a$ only holds for
positive numbers. State and prove this fact, making use of [the predicate
`IsPositive` from before](Padova2025.ProvingBasics.EvenOdd.html#IsPositive).

```
open import Padova2025.ProvingBasics.EvenOdd
```

```
lemma-succ-pred' : (a : ℕ) → {--}IsPositive a{--} → succ (pred a) ≡ a
-- Holify
lemma-succ-pred' a (case-succ _) = refl
```

<!--
-- EXERCISE: Show that the two functions "even?" and "even?'" have the same
values.
even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

even?' : ℕ → Bool
even?' zero            = true
even?' (succ zero)     = false
even?' (succ (succ n)) = even?' n

lemma-even?-even?' : (a : ℕ) → even? a ≡ even?' a
lemma-even?-even?' a = {!!}
-->
