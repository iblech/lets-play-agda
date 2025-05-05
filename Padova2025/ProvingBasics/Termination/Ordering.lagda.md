```
module Padova2025.ProvingBasics.Termination.Ordering where
```

# The standard ordering on the natural numbers

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Connectives
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```

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

≤-<-connex : (a b : ℕ) → a ≤ b ⊎ b < a
≤-<-connex zero     b        = left z≤n
≤-<-connex (succ a) zero     = right (s≤s z≤n)
≤-<-connex (succ a) (succ b) with ≤-<-connex a b
... | left  a≤b = left  (s≤s a≤b)
... | right b<a = right (s≤s b<a)

<-cmp : (a b : ℕ) → a ≡ b ⊎ (a < b ⊎ a > b)
<-cmp zero     zero     = left refl
<-cmp zero     (succ b) = right (left (s≤s z≤n))
<-cmp (succ a) zero     = right (right (s≤s z≤n))
<-cmp (succ a) (succ b) with <-cmp a b
... | left  a≡b         = left (cong succ a≡b)
... | right (left a<b)  = right (left (s≤s a<b))
... | right (right a>b) = right (right (s≤s a>b))

≤-antisymm : {a b : ℕ} → a ≤ b → b ≤ a → a ≡ b
≤-antisymm z≤n     z≤n     = refl
≤-antisymm (s≤s p) (s≤s q) = cong succ (≤-antisymm p q)

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
lookup : {P : ℕ → Set} {n m : ℕ} → All P (downFrom n) → m < n → P m
-- Holify
lookup {P} {succ n} {m} (p ∷ ps) m<n with ≤-<-connex n m
... | left  n≤m = subst P (≤-antisymm n≤m (pred-monotone m<n)) p
... | right m<n = lookup ps m<n
```
