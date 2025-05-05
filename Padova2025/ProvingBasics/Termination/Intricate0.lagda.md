```
module Padova2025.ProvingBasics.Termination.Intricate0 where
```

# An intricate zero function

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```

Let us consider the following recursive function definition.

```code
f : ℕ → ℕ
f zero     = zero
f (succ x) = f (f x)
```

Agda rejects this definition with the comment "Termination checking
failed". Agda's termination checker does not have any insight on what
the value of `f x` in the recursive call `f (f x)` will turn out to
be. But even though this fact is not obvious to Agda, the recursive
call terminates and the function `f` is constantly zero.


## Representing the function

To represent this function in Agda, we first introduce by
induction-recursion a predicate `Def` and a function `f₀`. For a
number `n`, `Def n` expresses that `n` belongs to the domain,
i.e. that the recursion terminates on input `n`. The function `f₀`
takes two inputs, a number `n` and a witness that the recursion
terminates on input `n`, and computes the result of the recursion.

```
data Def : ℕ → Set
f₀ : (n : ℕ) → Def n → ℕ

data Def where
  base : Def zero
  step : {x : ℕ} → (p : Def x) → Def (f₀ x p) → Def (succ x)

f₀ zero     _          = zero
f₀ (succ x) (step p q) = f₀ (f₀ x p) q
```


## Conditionally evaluating the function

Under the assumption that `n` belongs to the function's domain, we
can show that the value on input `n` is zero:

```
all0 : (n : ℕ) → (p : Def n) → f₀ n p ≡ zero
-- Holify
all0 zero     p          = refl
all0 (succ n) (step p q) = all0 (f₀ n p) q
```


## Verifying totality

This insight is enough to conclude that the function is defined on all
inputs.

```
total : (n : ℕ) → Def n
-- Holify
total zero     = base
total (succ n) = step (total n) (subst Def (sym (all0 n (total n))) base)
```

With totality in place, we can finally define `f` as follows.

```
f : ℕ → ℕ
f n = f₀ n (total n)
```
