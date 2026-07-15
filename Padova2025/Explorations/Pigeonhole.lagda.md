```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Explorations.Pigeonhole where
```

# The finitary pigeonhole principle

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProvingBasics.Termination.Ordering hiding (lookup)
```

The primary goal of this module is to state and give a direct proof of
the finitary pigeonhole principle in the following strong form: Every
vector of length `succ n`, consisting of elements of a type with `n`
elements, contains duplicates. Along the way, we will also formalize
results which are useful in the section on the infinite box problem
(TODO link).

TODO link to other formalizations

For every natural number `n`, the following definition sets up the prototypical
finite type `Fin n` of size `n`. Its inhabitants can be pictured as those
natural numbers which are strictly less than `n`.

```
data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)
```

```
fsucc-inj : {n : ℕ} → {x y : Fin n} → fsucc x ≡ fsucc y → x ≡ y
fsucc-inj {x = x} {y = y} refl = refl
```

```
toℕ : {n : ℕ} → Fin n → ℕ
toℕ fzero     = zero
toℕ (fsucc x) = succ (toℕ x)
```

```
toℕ-injective : {n : ℕ} {x y : Fin n} → toℕ x ≡ toℕ y → x ≡ y
toℕ-injective {x = fzero}   {y = fzero}   _ = refl
toℕ-injective {x = fsucc x} {y = fsucc y} p = cong fsucc (toℕ-injective (succ-injective p))
```

```
toℕ-bounded : {n : ℕ} (x : Fin n) → toℕ x < n
toℕ-bounded fzero     = s≤s z≤n
toℕ-bounded (fsucc x) = s≤s (toℕ-bounded x)
```

```
_≡?_ : {n : ℕ} → (x y : Fin n) → Dec (x ≡ y)
fzero ≡? fzero = yes refl
fzero ≡? fsucc y = no λ ()
fsucc x ≡? fzero = no λ ()
fsucc x ≡? fsucc y with x ≡? y
... | yes p = yes (cong fsucc p)
... | no  q = no λ p → q (fsucc-inj p)
```

We can collect the image of a function `Fin n → A` into a list:

```
tabulate-Fin : {A : Set} {n : ℕ} → (Fin n → A) → List A
-- Holify
tabulate-Fin {n = zero}   f = []
tabulate-Fin {n = succ n} f = f fzero ∷ tabulate-Fin (λ x → f (fsucc x))
```

```
∈-tabulate-Fin : {A : Set} {n : ℕ} (f : Fin n → A) (x : Fin n) → f x ∈ tabulate-Fin f
-- Holify
∈-tabulate-Fin f fzero     = here refl
∈-tabulate-Fin f (fsucc x) = there (∈-tabulate-Fin (λ y → f (fsucc y)) x)
```

And we can use elements of `Fin n` for indexing elements of lists of length `n`:

```
lookup : {A : Set} → (xs : List A) → Fin (length xs) → A
-- Holify
lookup (x ∷ xs) fzero     = x
lookup (x ∷ xs) (fsucc i) = lookup xs i
```

TODO finish, incorporating the work of Jacopo Piccione
