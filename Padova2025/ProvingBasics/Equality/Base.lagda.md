```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Equality.Base where
```

# Definition

In blackboard mathematics, "$x = y$" is an *assertion*, a *statement*. For
instance, this assertion might be true, or it might be false. In the Agda
community, `x ≡ y` is a type---the type of witnesses that `x` and `y` are
equal. For instance, this type could be inhabited, or it could be empty.

If in blackboard mathematics we would prove that $x = y$, in Agda we exhibit a
value of type `x ≡ y`.

The following three lines set up these types:

```code
infix 4 _≡_
data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a
```

::: Aside :::
The basic equality symbol `=` is used in Agda only for definitions. For
formulating assumptions or results involing equality, we use `≡`.
:::

::: More :::
For applications in some later parts of Let's play Agda, we will not adopt
the preceding code as our official definition of equality, even though
it would work just fine for almost all of our developments. The problem
with the definition above is that it only introduces equality types for
*small* types `X`, i.e. those which live in `Set`. But sometimes we would
also like to refer to equality between values of larger types, living in
`Set₁`, `Set₂` or beyond.

```
open import Agda.Primitive

infix 4 _≡_
data _≡_ {ℓ : Level} {X : Set ℓ} : X → X → Set ℓ where
  refl : {a : X} → a ≡ a
```
:::
