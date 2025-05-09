```
module Padova2025.Explorations.Uncountability.Impossible.Toy where
```

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProgrammingBasics.HigherOrder
open import Padova2025.ProvingBasics.Termination.Gas
open import Padova2025.Explorations.Uncountability.Applications

_◂_ : Bool → Cantor → Cantor
x ◂ xs = λ { zero → x ; (succ n) → xs n }

{-# NON_TERMINATING #-}
ε : (Cantor → Bool) → Cantor
ε P = x ◂ ε (P ∘ (x ◂_))
  where
  x : Bool
  x = P (false ◂ ε (P ∘ (false ◂_)))

has-root? : (Cantor → Bool) → Bool
has-root? P = P (ε P)

root : (Cantor → Bool) → Maybe (List Bool)
root P with P (ε P)
... | false = just (map (ε P) (zero ∷ one ∷ two ∷ three ∷ four ∷ []))
... | true  = nothing
```
