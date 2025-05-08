```
module Padova2025.ProvingBasics.Termination.Gas where
```

# Gas

```
data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just x  >>= f = f x

record 𝟙 : Set where
  constructor tt

module _ {A : Set} where
  From-just : Maybe A → Set
  From-just nothing  = 𝟙
  From-just (just _) = A

  from-just : (m : Maybe A) → From-just m
  from-just nothing  = tt
  from-just (just x) = x
```
