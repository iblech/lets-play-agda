```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Equality.General where
```

# General results on equality

```
open import Padova2025.ProvingBasics.Equality.Base
```


## Exercise: Symmetry

In blackboard mathematics, we have the basic result that $x = y$ implies $y = x$.
In Agda, we have a function which transforms values of type `x ≡ y` into
values of type `y ≡ x`. Fill in this hole:

```
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
-- Holify
sym refl = refl
```

::: Hint :::
1. First introduce a variable to the left of the `=` symbol, i.e. have the line
   read `sym p = ?`. Then reload the file using `C-c C-l`, else the hole will
   not know about the variable `p`.
2. Press `C-c ,` to ask Agda to print a summary of the situation.
3. Then do a case split on `p`.
4. Agda then recognizes that the only possibility for `p` is `refl`.
   Press `C-c ,` again to request a new printout of the situation.
   Notice that the situation has simplified.
5. Fill in the hole with `refl`, press `C-c C-SPACE` and then reload
   the file.
:::


## Exercise: Congruence

In blackboard mathematics, we have the basic result that an equation remains true
if the same operation is applied to its two sides: If $x = y$, then also $f(x) = f(y)$.
In Agda, we have a function which transformed values of type `x ≡ y` into
values of type `f x ≡ f y`:

```
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
-- Holify
cong f refl = refl
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
subst : {A : Set} {x y : A} → (F : A → Set) → x ≡ y → F x → F y
-- Holify
subst F refl s = s
```


## Exercise: Congruence for functions with two parameters

```
cong₂
  : {A B C : Set} {x x' : A} {y y' : B}
  → (f : A → B → C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
-- Holify
cong₂ f refl refl = refl
```

<!--
-- EXERCISE: Think about the expression "(⊥ ≡ ℕ)". Is it well-defined?
-- What would be its meaning?
-->


## Inequality

We can introduce inequality as follows.

```
open import Padova2025.ProvingBasics.Negation

infix 4 _≢_
_≢_ : {X : Set} → X → X → Set
a ≢ b = ¬ (a ≡ b)
```


## Pointwise equality

We will also use the notion that two functions have the same values,
called *pointwise equality*. ([We will later discuss](Padova2025.Cubical.Issues.FunctionExtensionality.html)
the relation of this notion to the more basic notion that two functions
are identical.)

```
infix 4 _≗_
_≗_ : {A B : Set} → (A → B) → (A → B) → Set
f ≗ g = (x : _) → f x ≡ g x
```

# TODO: with in exercise

## With abstraction

In some cases one needs to pattern match over a variable which its depends on the inputs
a function. The [Agda documentation](https://agda.readthedocs.io/en/stable/language/with-abstraction.html)
shows `filter` as an example.
```
{-# BUILTIN EQUALITY _≡_ #-}
```

```
module WithAbstraction where
  open import Padova2025.ProgrammingBasics.Booleans
  open import Padova2025.ProgrammingBasics.Lists
  open import Padova2025.ProgrammingBasics.Naturals.Base

  filter : {A : Set} → (A → Bool) → List A → List A
  filter f [] = []
  filter f (x ∷ xs) with f x
  ... | false = filter f xs
  ... | true  = x ∷ filter f xs
```
This `filter` implementation is very compact. The `with` removes the necessity of
introducing an auxiliary function which has only the task to pattern match the
`f x`. Now compare it to the implementation using an auxiliary function `aux`:
```
  filter' : {A : Set} → (A → Bool) → List A → List A
  filter' f [] = []
  filter' {A} f (x ∷ xs) = aux (f x)
    where
      aux : Bool → List A
      aux false = filter f xs
      aux true  = x ∷ filter f xs
```
It is much more boiler plate code.
The following function demonstrates the `with` abstraction
in a slightly trivial case:
```
  eq-to-bool : {A : Set} → (x y : A) → x ≡ y → Bool
  eq-to-bool x y refl = true
```
The same could be done via `with` an pattern matching over `p`.
The difference is, that after the `with` also a function of `p`
would be possible. So it is more general than the original definition:
```
  eq-to-bool' : {A : Set} → (x y : A) → x ≡ y → Bool
  eq-to-bool' x y p with p
  ... | refl = true
```
The `aux` function has the same purpose as the `with`:
```
  eq-to-bool'' : {A : Set} → (x y : A) → x ≡ y → Bool
  eq-to-bool'' x y p = aux p
    where
      aux : x ≡ y → Bool
      aux refl = true
```
Also nested `with`s are possible
```
  show-with-nested : {A : Set} → (x y : List A) → Bool
  show-with-nested x y with length x | length y
  ... | succ (succ zero)  | succ zero  = true
  ... | _                 | _          = false
```
Notice, that the order of the `with` abstractions matter and also notice that an overall nested
`with` is different to an additional `with` in one of the cases. `with` is particularily useful
for constructing counter examples in negations.

A with abstraction in a function definition makes a with abstraction in a proof about this
function necessary. The type in the step-case is `filter f (filter f (x ∷ xs) | f x) ≡ (filter f (x ∷ xs) | f x)` which means that we need a with abstraction over `f x` in this case.

The following example is also shown in the documentation and it is slightly more complicated
than anticipated:
```
  filter-idem : {A : Set} →
                (p : A → Bool) → (xs : List A) → (filter p (filter p xs)) ≡ (filter p xs)
  filter-idem f [] = refl
  filter-idem f (x ∷ xs) with f x in eq
  ... | false = filter-idem f xs
```
The documentation shows that the second part could simply be proven by using a `rewrite`
```
--  ... | true rewrite eq = cong (x ∷_) (filter-idem f xs)
```
but the `rewrite` has to be explained: With `in` after the `f x` we generate an equation `eq`
in every `with` clause, in our case `eq : f x ≡ false` and `eq : f x ≡ true`. For this we needed
the compiler pragma `{-# BUILTIN EQUALITY ≡ #-}` above. In the `false` case `eq` is not needed,
because we can trivially use the induction hypothesis as the element `x` is removed. The `true`
case is more complicated: The inner expression in `(filter f (...) | f x)` is now
`x ∷ filter f xs`. But to complete the proof, we need `x ∷_` outside of it. We are in the `true`
case of the `with` abstraction but have to re-establish the `f x` is still true. Therefore, we
have to perform another `with`. This is due to the fact that the outer `f x` is only seen after
we have established that the inner `f x` is true. `f x` cannot be generalized over (which means
substituted by a variable where we may case split), since it already has the value `true`.
Therefore, we need to use a dot pattern `.true`. But from this alone, Agda is not convinced
that this is actually true. We have to with-abstract over `eq` with the case `refl`
simultaneously.
```
  ... | true with f x  | eq
  ... |          .true | refl = cong (x ∷_) (filter-idem f xs)
```
This construction appears quite often in proofs and therefore is abbreviated by
`rewrite` above.

::: Aside :::
Let us switch the [`with ... in ...` syntactic
sugar](https://agda.readthedocs.io/en/stable/language/with-abstraction.html#with-abstraction-equality)
on.
:::
