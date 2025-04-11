```
module Padova2025.ProvingBasics.Equality.Lists where
```

# Results on lists

```
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Equality.Base
```

For the following exercise, note that `reverse (x ∷ xs)` is defined as
`reverse xs ∷ʳ x`.

```
lemma-reverse-∷ʳ : {A : Set} (ys : List A) (x : A) → reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
-- Holify
lemma-reverse-∷ʳ []       x = refl
lemma-reverse-∷ʳ (y ∷ ys) x = cong (λ zs → zs ∷ʳ y) (lemma-reverse-∷ʳ ys x)
```

```
lemma-reverse-reverse : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
-- Holify
lemma-reverse-reverse [] = refl
lemma-reverse-reverse (x ∷ xs) =
  trans (lemma-reverse-∷ʳ (reverse xs) x) (cong (x ∷_) (lemma-reverse-reverse xs))
```

::: Todo :::
Associativity of `_++_`
:::
