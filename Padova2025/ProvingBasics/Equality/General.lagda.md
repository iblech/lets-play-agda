```
module Padova2025.ProvingBasics.Equality.General where
```

# General results on identity

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

In blackboard mathematics, we have the basic result that an equation remain true
if the same operation is applied to its two sides: If $x = y$, then also $f(x) = f(x)$.
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
