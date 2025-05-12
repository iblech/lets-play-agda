```
module Padova2025.ComputationalContent.Fictions.InfinitelyMany (⊥ : Set) where
```

# Infinite subsequences

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.ComputationalContent.DoubleNegation (⊥)
```

```
not-true-is-false : {x : Bool} → ¬ (true ≡ x) → ¬ ¬ (false ≡ x)
-- Holify
not-true-is-false {false} p = return refl
not-true-is-false {true}  p = ⊥-elim (p refl)
```

The condition `Boundedly α P` expresses that the predicate `P` is satisfied by the values
of `α` only finitely often.
  
```
Boundedly : {X : Set} → (ℕ → X) → (X → Set) → Set
Boundedly f P = Σ[ a ∈ ℕ ] ((b : ℕ) → b ≥ a → ¬ P (f b))
```

The condition `Infinitely α P` expresses, in a positive way, that the values of `α`
satisfy `P` infinitely often.
 
```
Infinitely : {X : Set} → (ℕ → X) → (X → Set) → Set
Infinitely f P = (a : ℕ) → ¬ ¬ (Σ[ b ∈ ℕ ] b ≥ a × P (f b))
```

```
lemma : {X : Set} → {α : ℕ → X} {P : X → Set} → ¬ Boundedly α P → Infinitely α P
lemma {α = α} {P = P} p a = oracle ⟫= go
  where
  go : (∃[ b ] b ≥ a × P (α b)) ⊎ ((∃[ b ] b ≥ a × P (α b)) → ⊥) → ¬ ¬ (∃[ b ] b ≥ a × P (α b))
  go (left  q) = {--}return q{--}
  go (right q) = {--}⊥-elim (p (a , λ b b≥a Pb → q (b , b≥a , Pb))){--}
```

```
InfinitaryPigeonholePrinciple : (ℕ → Bool) → Set
InfinitaryPigeonholePrinciple α = Infinitely α (false ≡_) ⊎ Infinitely α (true ≡_)
```

```
infinitary-pigeonhole-principle : (α : ℕ → Bool) → ¬ ¬ InfinitaryPigeonholePrinciple α
infinitary-pigeonhole-principle α = oracle ⟫= go
  where
  go : Boundedly α (true ≡_) ⊎ ¬ Boundedly α (true ≡_) → ¬ ¬ InfinitaryPigeonholePrinciple α
  go (left  (a , p)) = {--}return (left  λ i →
    not-true-is-false (p (max i a) (max-inflationaryᵣ i a)) ⟫= λ q →
    return (max i a , max-inflationaryₗ i a , q)){--}
  go (right p)       = {--}return (right (lemma {P = (true ≡_)} p)){--}
```
