```
module Padova2025.ProvingBasics.Termination.WellFounded where
```

# Well-founded induction

```
module _ {X : Set} (_<_ : X → X → Set) where
  data Acc : X → Set where
    acc : {x : X} → ({y : X} → y < x → Acc y) → Acc x

  acc-inverse : {x : X} → Acc x → {y : X} → y < x → Acc y
  acc-inverse (acc f) = f
```

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Termination.Ordering
  hiding (_<_) renaming (_<'_ to _<_; base' to base; step' to step)
```

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


## The natural numbers are well-founded

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
