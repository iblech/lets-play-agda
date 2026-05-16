```
{-# OPTIONS --cubical-compatible #-}

open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.Explorations.Pigeonhole
import Padova2025.Recreational.Choice.Boxes.Base as Base
import Padova2025.Recreational.Choice.Boxes.Stage1 as Stage1

module Padova2025.Recreational.Choice.Boxes.Stage2
  (ℝ : Set) (n : ℕ) (R : Normalizer ℕ ℝ)
  (open Base ℝ n)
  (p : Player)
  (open Stage1 ℝ n p)
  (their-box-contents : I → ℝ) where
```

# Stage 2

```
open Normalizer R

known-bad-lane-indices : (q : Player) → List ℕ
known-bad-lane-indices q with q ≡? p
... | yes _   = []
... | no  q≢p = fst (rep≗* lane)
  where
  lane : Config
  lane i = their-box-contents (q , q≢p , i)

total-known-bad-lane-indices : List ℕ
total-known-bad-lane-indices = concat (tabulate-Fin known-bad-lane-indices)

M : ℕ
M = maximum total-known-bad-lane-indices

J : Set
J = Σ[ m ∈ ℕ ] m ≢ succ M

our-box-indices : J → ℕ
our-box-indices (m , _) = pack p m

not-opened : ¬ ((∅ ▷ their-box-indices ▷ our-box-indices) (pack p (succ M)))
not-opened (left  (left  ()))
not-opened (left  (right ((q , q≢p , m) , eq))) = q≢p  (fst (pack-injective {m = m} {m' = succ M} eq))
not-opened (right ((m , m≢sM) , eq))            = m≢sM (snd (pack-injective {m = m} {m' = succ M} eq))
```
