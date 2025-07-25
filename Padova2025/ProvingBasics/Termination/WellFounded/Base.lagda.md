```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Termination.WellFounded.Base where
```

# Well-founded relations

```
module _ {X : Set} (_<_ : X → X → Set) where
  data Acc : X → Set where
    acc : {x : X} → ({y : X} → y < x → Acc y) → Acc x

  acc-inverse : {x : X} → Acc x → {y : X} → y < x → Acc y
  acc-inverse (acc f) = f
```

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Termination.Ordering
  hiding (_<_) renaming (_<'_ to _<_; base' to base; step' to step)
```


## The natural numbers are well-founded

```
lemma-zero-is-accessible : Acc _<_ zero
lemma-zero-is-accessible = acc λ ()
```

```
lemma-one-is-accessible : Acc _<_ one
lemma-one-is-accessible = acc λ
  { base → lemma-zero-is-accessible
  }
```

```
lemma-two-is-accessible : Acc _<_ two
lemma-two-is-accessible = acc λ
  { base        → lemma-one-is-accessible
  ; (step base) → lemma-zero-is-accessible 
  }
```

```
lemma-three-is-accessible : Acc _<_ three
lemma-three-is-accessible = acc λ
  { base               → lemma-two-is-accessible
  ; (step base)        → lemma-one-is-accessible 
  ; (step (step base)) → lemma-zero-is-accessible 
  }
```

```
ℕ-wf : (n : ℕ) → Acc _<_ n
-- Holify
ℕ-wf zero = lemma-zero-is-accessible
ℕ-wf (succ n) = acc λ
  { base     → ℕ-wf n
  ; (step p) → acc-inverse _<_ (ℕ-wf n) p
  }
```


## Exercise: Well-founded relations are irreflexive

```
open import Padova2025.ProvingBasics.Negation
```

```
wf⇒irr : {X : Set} → (R : X → X → Set) → (a : X) → Acc R a → ¬ (R a a)
-- Holify
wf⇒irr R a (acc f) p = wf⇒irr R a (f p) p
```


## Exercise: No infinite descending sequences

```
no-descending-sequences : {X : Set} {_<_ : X → X → Set} → (α : ℕ → X) → ((n : ℕ) → α (succ n) < α n) → Acc _<_ (α zero) → ⊥
-- Holify
no-descending-sequences {X} {_<_} α desc (acc f) = no-descending-sequences α' desc' (f (desc zero))
  where
  α' : ℕ → X
  α' n = α (succ n)
  desc' : (n : ℕ) → α' (succ n) < α' n
  desc' n = desc (succ n)
```

::: Todo :::
Add remark about converse.
:::


## Exercise: Binary digits

```
digits₄ : ℕ → ℕ
digits₄ x = go x (ℕ-wf x)
  where
  go : (x : ℕ) → (gas : Acc _<_ x) → ℕ
  go zero       p       = {--}zero{--}
  go x@(succ _) (acc f) = {--}succ (go (half x) (f (<⇒<' (half-< _)))){--}
```

Unlike with using natural numbers as gas as in
[`digits₃`](Padova2025.ProvingBasics.Termination.Gas.html#digits₃),
no bailout case is needed. This recursion will always reach its base
case---and no extra proof of this fact is needed.

The verification of the fundamental identity `digits₄ x ≡ succ
(digits₄ (half x))` for positive `x` is best done in the greater
generality offered by the [next
module](Padova2025.ProvingBasics.Termination.WellFounded.Scheme.html).
