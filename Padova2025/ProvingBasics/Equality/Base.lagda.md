```
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

```
infix 4 _≡_
data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a
```

::: Aside :::
The basic equality symbol `=` is used in Agda only for definitions. For
formulating assumptions or results involing equality, we use `≡`.
:::
