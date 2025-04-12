```
module Padova2025.ProvingBasics.Equality.Booleans where
```

# Results on Booleans

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Operators
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```


## Exercise: Double negation

```
not² : (x : Bool) → not (not x) ≡ x
-- Holify
not² false = refl
not² true  = refl
```


## Exercise: Commutativity of logical AND

```
&&-comm : (x y : Bool) → (x && y) ≡ (y && x)
-- Holify
&&-comm false false = refl
&&-comm false true  = refl
&&-comm true  false = refl
&&-comm true  true  = refl
```
