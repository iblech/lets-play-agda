```
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Connectives

module Padova2025.VerifiedAlgorithms.InsertionSort.PostHoc
  (A : Set) (_≤_ : A → A → Set) (cmp? : (x y : A) → x ≤ y ⊎ y ≤ x) where
```

# Post-hoc verification

```
open import Padova2025.VerifiedAlgorithms.InsertionSort.Implementation A _≤_ cmp?
```

`IsOrdered xs` is the type of witnesses that the list `xs` is ordered.

```
data IsOrdered : List A → Set where
  empty     : IsOrdered []
  singleton : {x : A} → IsOrdered (x ∷ [])
  cons      : {x y : A} {ys : List A} → x ≤ y → IsOrdered (y ∷ ys) → IsOrdered (x ∷ (y ∷ ys))
```

```
lemma₀ : (x y : A) (ys : List A) → y ≤ x → IsOrdered (y ∷ ys) → IsOrdered (y ∷ insert x ys)
-- Holify
lemma₀ x y []       y≤x p = cons y≤x singleton
lemma₀ x y (z ∷ ys) y≤x (cons y≤z q) with cmp? x z
... | left  x≤z = cons y≤x (cons x≤z q)
... | right z≤x = cons y≤z (lemma₀ x z ys z≤x q)
```

```
lemma : (x : A) (ys : List A) → IsOrdered ys → IsOrdered (insert x ys)
-- Holify
lemma x []       p = singleton
lemma x (y ∷ ys) p with cmp? x y
... | left  x≤y = cons x≤y p
... | right y≤x = lemma₀ x y ys y≤x p
```

```
theorem : (xs : List A) → IsOrdered (sort xs)
-- Holify
theorem []       = empty
theorem (x ∷ xs) = lemma x (sort xs) (theorem xs)
```
