```
{-# OPTIONS --cubical #-}
module Padova2025.Cubical.FirstSteps where
```

# First steps

```
open import Cubical.Core.Everything
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base renaming (_≡_ to _≡ᵢ_)
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```


## Unordered pairs

```
data UnorderedPair (A : Set) : Set where
  pair : (x y : A) → UnorderedPair A
  swap : (x y : A) → pair x y ≡ pair y x
```


## Generalities on equality

```
refl' : {X : Set} {a : X} → a ≡ a
refl' {a = a} = λ i → a
```

```
symm' : {X : Set} {a b : X} → a ≡ b → b ≡ a
symm' p = λ i → p (~ i)
```

```
cong' : {X Y : Set} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b
cong' f p = {--}λ i → f (p i){--}
```

```
funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
-- Holify
funext h = λ i → λ x → h x i
```
