```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Explorations.Forcing.Orthogonal where
```

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.More
```

# Orthogonal forcing

This is work in progress to formalize a counterexample to the conjecture that
the cartesian product of streamless sets is streamless.

```
Good : {X : Set} → (X → X → Set) → (ℕ → X) → Set
Good _≈_ f = ∃[ i ] ∃[ j ] i ≢ j × f i ≈ f j 
```

```code
key-lemma : (f : ℕ → ℕ) (n : ℕ) → Good _≡_ f ⊎ ∃[ i ] ∃[ j ] i ≢ j × (f i ≥ n × f j ≥ n)
key-lemma f n = {!!}
-- Proof idea: Inspect the first n + 2 values of f.
-- There are only n numbers smaller than n.
-- So if these values are all distinct, at least two of them are guaranteed to be ≥ n.
-- Else we have duplicates.
```

```
data Cl {X : Set} (_≈_ : X → X → Set) : X → X → Set where
  ≈-base  : {a b : X} → a ≈ b → Cl _≈_ a b
  ≈-refl  : {a : X} → Cl _≈_ a a
  ≈-symm  : {a b : X} → Cl _≈_ a b → Cl _≈_ b a
  ≈-trans : {a b c : X} → Cl _≈_ a b → Cl _≈_ b c → Cl _≈_ a c
```

```
Cl' : {X : Set} → List (X × X) → (X → X → Set)
Cl' ps = Cl (λ a b → (a , b) ∈ ps)
```

```
_⫫_ : {X : Set} → (R S : X → X → Set) → Set
R ⫫ S = (a b : _) → R a b → S a b → a ≡ b
```

```
L : Set
L = List (ℕ × ℕ) × List (ℕ × ℕ)
```

```
data ∇ (P : L → Set) : L → Set where
  now    : {σ : L} → P σ → ∇ P σ
  laterₗ : {R S : List (ℕ × ℕ)} → (f : ℕ → ℕ) → ((R' S' : List (ℕ × ℕ)) → Good (Cl' (R ++ R')) f → ∇ P (R ++ R' , S ++ S')) → ∇ P (R , S)
  laterᵣ : {R S : List (ℕ × ℕ)} → (f : ℕ → ℕ) → ((R' S' : List (ℕ × ℕ)) → Good (Cl' (S ++ S')) f → ∇ P (R ++ R' , S ++ S')) → ∇ P (R , S)
```

```code
escape : {P : L → Set} (R S : List (ℕ × ℕ)) → Cl' R ⫫ Cl' S → ∇ P (R , S) → ∃[ R' ] ∃[ S' ] (Cl' R' ⫫ Cl' S') × P (R' , S')
escape = {!!}
```

```code
theorem : ¬ ∇ (λ (R , S) → ∃[ i ] ∃[ j ] i ≢ j × Cl' R i j × Cl' S i j) ([] , [])
theorem = {!!}
```
