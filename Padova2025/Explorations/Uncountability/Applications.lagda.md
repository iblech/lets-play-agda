```
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

We will prove it uncountable in two senses.

```
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
fixpoint-free {false} ()
fixpoint-free {true}  ()
```

```
fixpoint-free' : ¬ (∃[ x ] not x ≡ x)
fixpoint-free' (x , eq) = fixpoint-free eq
```

```
Cantor-uncountable₀ : (f : ℕ → Cantor) → Σ[ α ∈ Cantor ] ((n : ℕ) → α # f n)
Cantor-uncountable₀ f = (λ i → not (f i i)) , (λ n → (n , fixpoint-free))
```

```
Cantor-uncountable₁ : (f : ℕ → Cantor) → Σ[ α ∈ Cantor ] ¬ (∃[ n ] α ≗ f n)
Cantor-uncountable₁ f = (λ i → not (f i i)) , (λ (n , eq) → fixpoint-free (eq n))
```

```
Cantor-uncountable₂ : (f : ℕ → Cantor) → Σ[ α ∈ Cantor ] ¬ (∃[ n ] α ≡ f n)
Cantor-uncountable₂ f = (λ i → not (f i i)) , (λ (n , eq) → fixpoint-free (cong (λ g → g n) eq))
```

```
Cantor-uncountable₁' : ¬ (Σ[ f ∈ (ℕ → Cantor) ] IsWeaklySplitSurjective _≗_ f)
Cantor-uncountable₁' (f , weak-split-surjectivity) = fixpoint-free' (fix₀ weak-split-surjectivity)
  where
  open L f not
```

```
Cantor-uncountable₂' : ¬ (Σ[ f ∈ (ℕ → Cantor) ] IsSplitSurjective f)
Cantor-uncountable₂' (f , split-surjectivity) = fixpoint-free' (fix₀ weak-split-surjectivity)
  where
  weak-split-surjectivity : IsWeaklySplitSurjective _≗_ f
  weak-split-surjectivity h = fst (split-surjectivity h) , λ n → cong (λ g → g n) (snd (split-surjectivity h))
  open L f not
```


## Uncountability of the universe

Using similar methods, we can also show that the type `Set` of all small types is not countable.

Martín Escardó has explored this topic
[in great detail](https://martinescardo.github.io/TypeTopology/LawvereFPT.html).
