```
module Padova2025.ComputationalContent.Fictions.Minima (⊥ : Set) where
```

# Minima

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.ProvingBasics.Termination.WellFounded.Base
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ComputationalContent.DoubleNegation (⊥)
```

## Classical result

::: Todo :::
Fill in.
:::


## Constructive result

```
go : (α : ℕ → ℕ) → (i : ℕ) → Acc _<'_ (α i) → ¬ ¬ (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ α i ≤ α j))
go α i (acc f) = oracle {Σ[ j ∈ ℕ ] α j < α i} ⟫= g
  where
  g : ((Σ[ j ∈ ℕ ] α j < α i) ⊎ ((Σ[ j ∈ ℕ ] α j < α i) → ⊥)) →
    ¬ ¬ (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ α i ≤ α j))
  g (left  (j , p)) = {--}go α j (f (<⇒<' p)){--}
  g (right q)       = {--}return (i , h){--}
    where
    h : (j : ℕ) → ¬ ¬ (α i ≤ α j)
    h j with ≤-<-connex (α i) (α j)
    ... | left  αi≤αj = {--}return αi≤αj{--}
    ... | right αj<αi = {--}⊥-elim (q (j , αj<αi)){--}
```

```
minimum : (α : ℕ → ℕ) → ¬ ¬ (Σ[ i ∈ ℕ ] ((j : ℕ) → ¬ ¬ α i ≤ α j))
-- Holify
minimum α = go α zero (ℕ-wf (α zero))
```


## Variant of inhabited sets of natural numbers

::: Todo :::
Fill in.
:::
