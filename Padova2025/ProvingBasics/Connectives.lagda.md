```
module Padova2025.ProvingBasics.Connectives where
```

# Logical connectives 🚧

```
open import Padova2025.ProgrammingBasics.Lists
open import Agda.Primitive
```

```
-- In Haskell, Either A B
infixr 1 _⊎_
data _⊎_ (A : Set) (B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
```

```
record Σ {ℓ ℓ' : Level} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public
infixr 4 _,_

∃-syntax : {ℓ ℓ' : Level} {A : Set ℓ} → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
∃-syntax = Σ _

syntax ∃-syntax (λ x → B) = ∃[ x ] B

infixr 2 _×_
_×_ : (A : Set) (B : Set) → Set
A × B = Σ A (λ _ → B)
```


## Exercise: Even or odd

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.DependentFunctions
open import Padova2025.ProvingBasics.EvenOdd
open import Padova2025.ProvingBasics.Negation
```

```
even-or-odd : (x : ℕ) → Even x ⊎ Odd x
-- Holify
even-or-odd zero            = left base-even
even-or-odd (succ zero)     = right base-odd
even-or-odd (succ (succ x)) with even-or-odd x
... | left  p = left  (step-even p)
... | right p = right (step-odd p)
```

```
not-odd-implies-even : (x : ℕ) → ¬ Odd x → Even x
-- Holify
not-odd-implies-even x p with even-or-odd x
... | left  q = q
... | right q = ⊥-elim (p q)
```


## Remark: A variety of formalizations of evenness

[Back when introducing
predicates](Padova2025.ProvingBasics.EvenOdd.html), we have chosen one
particular definition of evenness. But other formalizations are also
possible. Let us collect here all the auxiliary results showing that
several of those notions coincide.

```
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

```
Even₁ Even₂ Even₃ Even₄ : ℕ → Set

Even₁ n = Even n
Even₂ n = ¬ Odd n
Even₃ n = Odd (succ n)
Even₄ n = ∃[ m ] (n ≡ twice m)
```

```
1⇒2 : {n : ℕ} → Even₁ n → Even₂ n
2⇒1 : {n : ℕ} → Even₂ n → Even₁ n
1⇒3 : {n : ℕ} → Even₁ n → Even₃ n
3⇒1 : {n : ℕ} → Even₃ n → Even₁ n
1⇒4 : {n : ℕ} → Even₁ n → Even₄ n
4⇒1 : {n : ℕ} → Even₄ n → Even₁ n

1⇒2 = even-and-odd
2⇒1 = not-odd-implies-even _
1⇒3 = succ-even
3⇒1 = succ-even'
1⇒4 p = half _ , even-twice p
4⇒1 (m , p) = subst Even (sym p) (twice-even m)
```


## All and Any

```
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
```

```
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
```
