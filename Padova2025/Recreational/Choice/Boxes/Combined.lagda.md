```
{-# OPTIONS --cubical-compatible #-}

open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Connectives.More

module Padova2025.Recreational.Choice.Boxes.Combined (ℝ : Set) (n : ℕ) where
```

# Combined

```
open import Padova2025.Recreational.Choice.Boxes.Base ℝ n
import Padova2025.Recreational.Choice.Boxes.Stage1 ℝ n as Stage1
import Padova2025.Recreational.Choice.Boxes.Stage2 ℝ n as Stage2
import Padova2025.Recreational.Choice.Boxes.Stage3 ℝ n as Stage3
```

```
assemble : Normalizer ℕ ℝ → TeamStrategy
assemble R p =
  let open Stage1 p
  in  peek their-box-indices λ their-box-contents →
  let open Stage2 R p their-box-contents
  in  peek our-box-indices λ our-box-contents →
  let open Stage3 R p their-box-contents our-box-contents
  in  guess (pack p (succ M)) not-opened our-guess
```
