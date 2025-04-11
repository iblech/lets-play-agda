```
module Padova2025.ProvingBasics.Equality.NaturalNumbers where
```

# Identities involving natural numbers

```
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
```

```
lemma-+-associative : (a b c : ℕ) → (a + (b + c)) ≡ ((a + b) + c)
-- Holify
lemma-+-associative zero     b c = refl
lemma-+-associative (succ a) b c = cong succ (lemma-+-associative a b c)
```

```
lemma-+-zero : (a : ℕ) → (a + zero) ≡ a
-- Holify
lemma-+-zero zero     = refl
lemma-+-zero (succ a) = cong succ (lemma-+-zero a)
```

```
lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
-- Holify
lemma-+-succ zero     b = refl
lemma-+-succ (succ a) b = cong succ (lemma-+-succ a b)
```

```
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
-- Holify
lemma-+-commutative zero     b = symm (lemma-+-zero b)
lemma-+-commutative (succ a) b =
  trans (cong succ (lemma-+-commutative a b)) (symm (lemma-+-succ b a))
```

<!--

lemma-+-succ : (a b : ℕ) → (a + succ b) ≡ succ (a + b)
lemma-+-succ a b = {!!}

-- EXERCISE: Verify that addition is commutative.
lemma-+-commutative : (a b : ℕ) → (a + b) ≡ (b + a)
lemma-+-commutative a b = {!!}

-- EXERCISE: Verify that addition is associative.

-- EXERCISE: Verify the distributive law. Similar as the implementation/proof
-- of lemma-+-commutative, the result will not be easy to read.
-- By a technique called "equational reasoning", to be introduced next time,
-- we will be able to clean up the proof.
lemma-distributive : (a b c : ℕ) → ((a + b) · c) ≡ ((a · c) + (b · c))
lemma-distributive a b c = {!!}
-->
