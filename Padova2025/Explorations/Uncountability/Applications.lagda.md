```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Explorations.Uncountability.Applications where
```

# Applications

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Connectives.Existential
import Padova2025.Explorations.Uncountability.Lawvere as L
```


## Uncountability of the Cantor space

A premier example for an uncountable type is the Cantor space, the
type of infinite binary sequences.

```
Cantor : Set
Cantor = ℕ → Bool
```

We will prove it uncountable in five senses.

```
-- A strong notion of two functions being distinct.
_#_ : {A B : Set} → (A → B) → (A → B) → Set
f # g = ∃[ a ] f a ≢ g a
```

```
IsSplitSurjective : {A B : Set} → (A → B) → Set
IsSplitSurjective f = (y : _) → ∃[ x ] y ≡ f x
```

```
IsWeaklySplitSurjective : {A B : Set} → (B → B → Set) → (A → B) → Set
IsWeaklySplitSurjective _≈_ f = (y : _) → ∃[ x ] y ≈ f x
```

```
fixpoint-free : {x : Bool} → not x ≡ x → ⊥
-- Holify
fixpoint-free {false} ()
fixpoint-free {true}  ()
```

```
fixpoint-free' : ¬ (∃[ x ] not x ≡ x)
-- Holify
fixpoint-free' (x , eq) = fixpoint-free eq
```

The following is the strongest form of the result that the Cantor space is
uncountable: For every potential enumeration `f : ℕ → Cantor`, there is
a sequence `α : Cantor` such that for every number `n`, there is a position
at which the sequences `α` and `f n` differ.

```
uncountable₀ : (f : ℕ → Cantor) → Σ[ α ∈ Cantor ] ((n : ℕ) → α # f n)
-- Holify
uncountable₀ f = (λ i → not (f i i)) , (λ n → (n , fixpoint-free))
```

We can then gradually weaken the result, in order to obtain statements
which are more readily recognizable as uncountability assertions.

```
uncountable₁ : (f : ℕ → Cantor) → Σ[ α ∈ Cantor ] ¬ (∃[ n ] α ≗ f n)
-- Holify
uncountable₁ f with uncountable₀ f
... | α , p = α , λ (n , eq) → snd (p n) (eq (fst (p n)))
```

```
uncountable₂ : (f : ℕ → Cantor) → Σ[ α ∈ Cantor ] ¬ (∃[ n ] α ≡ f n)
-- Holify
uncountable₂ f with uncountable₁ f
... | α , p = α , λ (n , eq) → p (n , λ x → cong (λ g → g x) eq)
```

```
uncountable₁' : ¬ (Σ[ f ∈ (ℕ → Cantor) ] IsWeaklySplitSurjective _≗_ f)
-- Holify
uncountable₁' (f , weak-split-surjectivity) = fixpoint-free' (fix₀ weak-split-surjectivity)
  where
  open L f not
-- Alternatively as a consequence of uncountable₁:
-- uncountable₁' (f , weak-split-surjectivity) with uncountable₁ f
-- ... | α , p = p (weak-split-surjectivity α)
```

```
uncountable₂' : ¬ (Σ[ f ∈ (ℕ → Cantor) ] IsSplitSurjective f)
-- Holify
uncountable₂' (f , split-surjectivity) = fixpoint-free' (fix₀ weak-split-surjectivity)
  where
  weak-split-surjectivity : IsWeaklySplitSurjective _≗_ f
  weak-split-surjectivity h = fst (split-surjectivity h) , λ n → cong (λ g → g n) (snd (split-surjectivity h))
  open L f not
-- Alternatively as a consequence of uncountable₂:
-- uncountable₂' (f , split-surjectivity) with uncountable₂ f
-- ... | α , p = p (split-surjectivity α)
```


## Uncountability of the Baire space

```
Baire : Set
Baire = ℕ → ℕ
```

```
baire-uncountable₀ : (f : ℕ → Baire) → Σ[ α ∈ Baire ] ((n : ℕ) → α # f n)
-- Holify
baire-uncountable₀ f = (λ i → succ (f i i)) , (λ n → (n , succ-fixpoint-free))
  where
  succ-fixpoint-free : {x : ℕ} → succ x ≢ x
  succ-fixpoint-free ()
```


## Uncountability of the universe

Using similar methods, we can also show that the type `Set` of all small types is not countable.

Martín Escardó has explored this topic
[in great detail](https://martinescardo.github.io/TypeTopology/LawvereFPT.html).
