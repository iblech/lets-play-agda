```
module Padova2025.ComputationalContent.Blueprints.Minima where
```

# Minima

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.ProvingBasics.Termination.WellFounded.Base
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
```

```
postulate
  oracle : {A : Set} → A ⊎ ¬ A
```

```
go : (α : ℕ → ℕ) → (i : ℕ) → Acc _<'_ (α i) → Σ[ i ∈ ℕ ] ((j : ℕ) → α i ≤ α j)
go α i (acc f) with oracle {Σ[ j ∈ ℕ ] α j < α i}
... | left  (j , p) = {--}go α j (f (<⇒<' p)){--}
... | right q       = {--}(i , h){--}
  where
  h : (j : ℕ) → α i ≤ α j
  h j with ≤-<-connex (α i) (α j)
  ... | left  αi≤αj = {--}αi≤αj{--}
  ... | right αj<αi = {--}⊥-elim (q (j , αj<αi)){--}
```

```
minimum : (α : ℕ → ℕ) → Σ[ i ∈ ℕ ] ((j : ℕ) → α i ≤ α j)
-- Holify
minimum α = go α zero (ℕ-wf (α zero))
```
