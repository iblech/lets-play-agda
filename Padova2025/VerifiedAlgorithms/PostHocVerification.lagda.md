```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.VerifiedAlgorithms.PostHocVerification where
```

# Post-hoc verification

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.DecisionProcedures
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

> *Beware of bugs in the above code; I have only proved it correct, not tried it.* \
> ―Donald Knuth

In *post-hoc verification*, we leverage the expressivity and strength of Agda to
verify the correctness of (separatedly) implemented algorithms.

For instance, the purpose of the
[`eq? : ℕ → ℕ → Bool`](Padova2025.ProgrammingBasics.Naturals.DecisionProcedures.html#eq?)
function is to decide whether its two inputs agree. But does our implementation
really meet this challenge? In ordinary programming languages without
dependent types, we might test the function with particular examples (perhaps
[randomly generated](https://jesper.sikanda.be/posts/quickcheck-intro.html)),
or have a close look at the implementation, perhaps ask colleagues to share a
review, ... Thanks to the expressivity of Agda's type system, in Agda we can
instead formally prove the correctness.

::: Todo :::
Expand.
:::

```
eq?-correct₁ : (x y : ℕ) → eq? x y ≡ true → x ≡ y
-- Holify
eq?-correct₁ zero     zero     p = refl
eq?-correct₁ (succ x) (succ y) p = cong succ (eq?-correct₁ x y p)
```

```
eq?-correct₂ : (x y : ℕ) → x ≡ y → eq? x y ≡ true
-- Holify
eq?-correct₂ zero zero p = refl
eq?-correct₂ (succ x) (succ y) p = eq?-correct₂ x y (succ-injective p)
```


## Exercise: Correctness of the decision procedure for inequality

```
open import Padova2025.ProvingBasics.Termination.Ordering
```

```
≤?-correct₁ : (x y : ℕ) → ≤? x y ≡ true → x ≤ y
-- Holify
≤?-correct₁ zero     y        p = z≤n
≤?-correct₁ (succ x) (succ y) p = s≤s (≤?-correct₁ x y p)
```

```
≤?-correct₂ : (x y : ℕ) → x ≤ y → ≤? x y ≡ true
-- Holify
≤?-correct₂ x        y        z≤n     = refl
≤?-correct₂ (succ x) (succ y) (s≤s p) = ≤?-correct₂ x y p
```


## Exercise: Correctness of the decision procedure for evenness

```
open import Padova2025.ProvingBasics.EvenOdd
```

```
even?-correct₁ : (x : ℕ) → even? x ≡ true → Even x
-- Holify
even?-correct₁ zero            p = base-even
even?-correct₁ (succ (succ x)) p = step-even (even?-correct₁ x p)
```

```
even?-correct₂ : {x : ℕ} → Even x → even? x ≡ true
-- Holify
even?-correct₂ base-even     = refl
even?-correct₂ (step-even p) = even?-correct₂ p
```


## Exercise: Correctness of the subtraction function

```
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```

```
∸-correct : (x y : ℕ) → x ≥ y → y + (x ∸ y) ≡ x
-- Holify
∸-correct x        zero     x≥y       = refl
∸-correct (succ x) (succ y) (s≤s x≥y) = cong succ (∸-correct x y x≥y)
```
