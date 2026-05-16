```
{-# OPTIONS --cubical-compatible #-}

open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.Explorations.Pigeonhole

module Padova2025.Recreational.Choice.Boxes.Base (ℝ : Set) (n : ℕ) where
```

# Intro

An evil monster prepares a secret room containing infinitely many opaque
boxes. The boxes are numbered by the naturals and each box contains a real
number of the monster's choosing.

One by one, the evil monster privately guides the members of a team of `n`
mathematicians into the room, with the other members waiting outside.
While in the room, each mathematician may open as many boxes as they
wish, even infinitely many, inspecting their contents. They may base their
decision as to which boxes to open on the contents they have seen so far.
The only requirement is that they keep one box of their choosing untouched:
The monster will ask them for a guess regarding the contents of that box.

The mathematicians win as a team if and only if at most one of them guesses
incorrectly. As usual, communication among the team is allowed only
beforehand. Between successive visits to the room, the room is reset
to its original state (so all the opened boxes are closed again).

```
Config : Set
Config = ℕ → ℝ
```

```
Player : Set
Player = Fin n
```

```
∅ : ℕ → Set
∅ _ = ⊥
```

```
infixl 5 _▷_
_▷_ : {I : Set} → (ℕ → Set) → (I → ℕ) → (ℕ → Set)
Opened ▷ xs = λ x → Opened x ⊎ ∃[ i ] xs i ≡ x
```

For a predicate `Opened : ℕ → Set`, the type `PlayerStrategy Opened` is the type of all
possible strategies which are valid in the sense of not offering a guess for an already
opened box.

```
data PlayerStrategy (Opened : ℕ → Set) : Set₁ where
  guess : (x : ℕ) → ¬ Opened x → ℝ → PlayerStrategy Opened
  peek  : {I : Set} → (xs : I → ℕ) → ((I → ℝ) → PlayerStrategy (Opened ▷ xs)) → PlayerStrategy Opened
```

```
guessesCorrectly : {Opened : ℕ → Set} → PlayerStrategy Opened → Config → Set
guessesCorrectly (guess x _ y) c = y ≡ c x
guessesCorrectly (peek xs k)   c = guessesCorrectly (k (λ i → c (xs i))) c
```

```
TeamStrategy : Set₁
TeamStrategy = Player → PlayerStrategy ∅
```

```
isSuccessful : TeamStrategy → Set
isSuccessful s
  = (c : Config)
  → (q q' : Player) → ¬ guessesCorrectly (s q)  c → ¬ guessesCorrectly (s q') c
  → q ≡ q'
```


## Lane arithmetic

```
pack : Player → ℕ → ℕ
pack p zero     = toℕ p
pack p (succ m) = n + pack p m

pack-≥ : (p : Player) (m : ℕ) → pack p (succ m) ≥ n
pack-≥ p m = +-inflationaryₗ n (pack p m)

pack-injective : {q q' : Player} {m m' : ℕ} → pack q m ≡ pack q' m' → q ≡ q' × m ≡ m'
pack-injective {q} {q'} {zero}   {zero}    eq = toℕ-injective eq , refl
pack-injective {q} {q'} {zero}   {succ m'} eq = ⊥-elim (<-irreflexive' (≤-trans (pack-≥ q' m') (≡⇒≤ (sym eq))) (toℕ-bounded q))
pack-injective {q} {q'} {succ m} {zero}    eq = ⊥-elim (<-irreflexive' (≤-trans (pack-≥ q m) (≡⇒≤ eq)) (toℕ-bounded q'))
pack-injective {q} {q'} {succ m} {succ m'} eq with pack-injective (+-cancelₗ n _ _ eq)
... | q≡q' , m≡m' = q≡q' , cong succ m≡m'
```

```
insert : (j : ℕ) → (Σ[ i ∈ ℕ ] i ≢ j → ℝ) → ℝ → Config
insert j c x i with eq? i j
... | left  _   = x
... | right i≢j = c (i , i≢j)
```

```
insert-≗* : (j : ℕ) → (c : Config) → (x : ℝ) → insert j (λ (i , _) → c i) x ≗* c
insert-≗* j c x = j ∷ [] , go
  where
  go : (i : ℕ) → insert j (λ (i , _) → c i) x i ≡ c i ⊎ i ∈ (j ∷ [])
  go i with eq? i j
  ... | left  refl = right (here refl)
  ... | right _    = left refl
```

TODO
cite Gabay–O'Connor and Hardin & Taylor
