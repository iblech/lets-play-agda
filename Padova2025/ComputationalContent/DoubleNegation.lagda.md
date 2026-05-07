```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ComputationalContent.DoubleNegation (⊥ : Set) where
```

# Sarcastic interpretation of classical logic

::: Todo :::
Explain.
:::

```
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProgrammingBasics.Lists
```

```
infix 3 ¬_
¬_ : Set → Set  -- enter `¬` as `\neg`
¬ P = (P → ⊥)
```

```
return : {A : Set} → A → ¬ ¬ A
-- Holify
return x = λ k → k x
```

```
⊥-elim : {A : Set} → ⊥ → ¬ ¬ A
-- Holify
⊥-elim x = λ k → x
```

```
escape : ¬ ¬ ⊥ → ⊥
-- Holify
escape f = f (λ x → x)
```

```
oracle : {A : Set} → ¬ ¬ (A ⊎ ¬ A)
-- Holify
oracle f = f (right (λ x → f (left x)))
```

```
infixl 1 _>>=_ _⟫=_
```

```
_>>=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
-- Holify
_>>=_ m f = λ k → m (λ x → f x k)
```

```
_⟫=_ : {A B : Set} → ¬ ¬ A → (A → ¬ ¬ B) → ¬ ¬ B
_⟫=_ = _>>=_
```

```
liftA2 : {A B C : Set} → (A → B → C) → ¬ ¬ A → ¬ ¬ B → ¬ ¬ C
-- Holify
liftA2 f x y = do
  x' ← x
  y' ← y
  return (f x' y')
```

```
sequence : {X : Set} {P : X → Set} {xs : List X} → All (λ x → ¬ ¬ P x) xs → ¬ ¬ All P xs
-- Holify
sequence []       = return []
sequence (p ∷ ps) = liftA2 _∷_ p (sequence ps)
-- Alternatively:
-- sequence (p ∷ ps) = do
--   p'  ← p
--   ps' ← sequence ps
--   return (p' ∷ ps')
```
