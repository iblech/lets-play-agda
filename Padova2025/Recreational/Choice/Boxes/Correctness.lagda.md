```
{-# OPTIONS --cubical-compatible #-}

open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.Explorations.Pigeonhole
import Padova2025.Recreational.Choice.Boxes.Base as Base

module Padova2025.Recreational.Choice.Boxes.Correctness
  (ℝ : Set) (n : ℕ) (R : Normalizer ℕ ℝ)
  (open Base ℝ n)
  (c : Config)
  where
```

# Correctness

```
import Padova2025.Recreational.Choice.Boxes.Stage1 ℝ n as Stage1
import Padova2025.Recreational.Choice.Boxes.Stage2 ℝ n as Stage2
import Padova2025.Recreational.Choice.Boxes.Stage3 ℝ n as Stage3
open import Padova2025.Recreational.Choice.Boxes.Combined ℝ n
```

```
infixr 9 _∘_
_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g (f x)
```

```
open Normalizer R
```

```
module PlayerView (p : Player) where
  open Stage1 p public
  their-box-contents : I → ℝ
  their-box-contents = c ∘ their-box-indices

  open Stage2 R p their-box-contents public
  our-box-contents : J → ℝ
  our-box-contents = c ∘ our-box-indices

  open Stage3 R p their-box-contents our-box-contents public

lane : Player → Config
lane p = c ∘ pack p

rep-is-truthful : Player → Set
rep-is-truthful p = rep (lane p) (succ M) ≡ (lane p) (succ M)
  where open PlayerView p

truthful-causes-win : (p : Player) → rep-is-truthful p → guessesCorrectly (assemble R p) c
truthful-causes-win p eq = trans (respects (insert-≗* (succ M) (lane p) dummy) (succ M)) eq
  where open PlayerView p

in-bad-list
  : (p p' : Player) → p ≢ p' → (x : ℕ) → rep (lane p) x ≢ lane p x
  → x ∈ PlayerView.known-bad-lane-indices p' p
in-bad-list p p' p≢p' x neq with p ≡? p'
... | yes p≡p' = ⊥-elim (p≢p' p≡p')
... | no _     = ∨-not₂ (∨-comm (snd (rep≗* (lane p)) x)) neq

bound : (p p' : Player) → p ≢ p' → ¬ rep-is-truthful p → succ (PlayerView.M p) ≤ PlayerView.M p'
bound p p' p≢p' p-l = maximum-≥ _ _ (∈-concat (in-bad-list p p' p≢p' (succ (PlayerView.M p)) p-l) (∈-tabulate-Fin _ p))

one-loser : (p p' : Player) → ¬ rep-is-truthful p → ¬ rep-is-truthful p' → p ≡ p'
one-loser p p' p-l p'-l with p ≡? p'
... | yes p≡p' = p≡p'
... | no  p≢p' = ⊥-elim (<-irreflexive'' (bound p p' p≢p' p-l) (bound p' p (p≢p' ∘ sym) p'-l))

correct : (p p' : Player) → ¬ guessesCorrectly (assemble R p) c → ¬ guessesCorrectly (assemble R p') c → p ≡ p'
correct p p' ¬gc-p ¬gc-p' =
  one-loser p p' (contraposition (truthful-causes-win p) ¬gc-p) (contraposition (truthful-causes-win p') ¬gc-p')
```

theorem : (R : Normalizer ℕ ℝ) → isSuccessful (assemble R)
theorem R c = Correctness.correct R c
