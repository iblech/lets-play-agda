```
module Padova2025.VerifiedAlgorithms.PostHocVerification where
```

# Post-hoc verification 🚧

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.DecisionProcedures
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

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
