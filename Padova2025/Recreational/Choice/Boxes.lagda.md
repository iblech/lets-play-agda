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
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.Explorations.Pigeonhole

module Padova2025.Recreational.Choice.Boxes (ℝ : Set) (n : ℕ) where
```

```
infixr 9 _∘_
_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g (f x)
```

# The infinite boxes problem

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

TODO turn into exercises

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
Opened ▷ xs = λ x → Opened x ⊎ Σ[ i ∈ _ ] xs i ≡ x
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
  = (c : Config) (q q' : Player)
  → ¬ guessesCorrectly (s q)  c
  → ¬ guessesCorrectly (s q') c
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
pack-injective {q} {q'} {succ m}  {zero}   eq = ⊥-elim (<-irreflexive' (≤-trans (pack-≥ q m) (≡⇒≤ eq)) (toℕ-bounded q'))
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


## Stage 1: Peeking at the other player's lanes

We commit to inspect each other player's lane fully.

```
module Stage1 (p : Player) where
  I : Set
  I = Σ[ q ∈ Player ] q ≢ p × ℕ

  their-box-indices : I → ℕ
  their-box-indices (q , _ , m) = pack q m
```


## Stage 2: Peeking at our boxes (with one exception)

```
module Stage2 (R : Normalizer ℕ ℝ) (p : Player) (their-box-contents : Stage1.I p → ℝ) where
  open Normalizer R
  open Stage1 p

  lane : (q : Player) → q ≢ p → Config
  lane q q≢p x = their-box-contents (q , q≢p , x)

  known-bad-lane-indices : (q : Player) → List ℕ
  known-bad-lane-indices q with q ≡? p
  ... | yes _   = []
  ... | no  q≢p = fst (rep≗* (lane q q≢p))

  M : ℕ
  M = maximum (concat (tabulate-Fin known-bad-lane-indices))

  J : Set
  J = Σ[ m ∈ ℕ ] m ≢ succ M

  our-box-indices : J → ℕ
  our-box-indices (m , _) = pack p m

  not-opened : ¬ ((∅ ▷ their-box-indices ▷ our-box-indices) (pack p (succ M)))
  not-opened (left  (left  ()))
  not-opened (left  (right ((q , q≢p , m) , eq))) = q≢p  (fst (pack-injective {m = m} {m' = succ M} eq))
  not-opened (right ((m , m≢sM) , eq))            = m≢sM (snd (pack-injective {m = m} {m' = succ M} eq))
```


## Stage 3: Offering our guess for the remaining box

```
module Stage3 (R : Normalizer ℕ ℝ) (p : Player) (their-box-contents : Stage1.I p → ℝ) (our-box-contents : Stage2.J R p their-box-contents → ℝ) where
  open Normalizer R
  open Stage1 p
  open Stage2 R p their-box-contents

  dummy : ℝ
  dummy = our-box-contents (zero , λ ())

  -- The boxes of our lane, with `dummy` inserted as placeholder for the unique unopened box
  mostly-our-lane : Config
  mostly-our-lane = insert (succ M) our-box-contents dummy

  our-guess : ℝ
  our-guess = rep mostly-our-lane (succ M)
```


## Assembling all three stages

```
assemble : Normalizer ℕ ℝ → TeamStrategy
assemble R p =
  let open Stage1 p
  in  peek their-box-indices λ their-box-contents →
  let open Stage2 R p their-box-contents
  in  peek our-box-indices λ our-box-contents →
  let open Stage3 R p their-box-contents our-box-contents
  in  guess (pack p (succ M)) not-opened our-guess
```

```
module Correctness (R : Normalizer ℕ ℝ) (c : Config) where
  open Normalizer R

  module PlayerView (p : Player) where
    open Stage1 p public
    their-box-contents = c ∘ their-box-indices

    open Stage2 R p their-box-contents hiding (lane) public
    our-box-contents = c ∘ our-box-indices

    open Stage3 R p their-box-contents our-box-contents public

  lane : Player → Config
  lane q m = c (pack q m)

  bad-lane-indices : Player → List ℕ
  bad-lane-indices q = fst (rep≗* (lane q))

  loses : Player → Set
  loses p = succ M ∈ bad-lane-indices p
    where open PlayerView p

  bad-list-≢ : (p q : Player) → q ≢ p → PlayerView.known-bad-lane-indices p q ≡ bad-lane-indices q
  bad-list-≢ p q q≢p with q ≡? p
  ... | yes q≡p = ⊥-elim (q≢p q≡p)
  ... | no  _   = refl

  in-bad-list
    : (p p' : Player) → p ≢ p' → (x : ℕ) → x ∈ bad-lane-indices p
    → x ∈ PlayerView.known-bad-lane-indices p' p
  in-bad-list p p' p≢p' x x∈bad =
    subst (x ∈_) (sym (bad-list-≢ p' p p≢p')) x∈bad

  bound : (p p' : Player) → p ≢ p' → loses p → succ (PlayerView.M p) ≤ PlayerView.M p'
  bound p p' p≢p' p-l =
    maximum-≥ _ _
      (∈-concat (in-bad-list p p' p≢p' _ p-l)
                (∈-tabulate-Fin _ p))

  one-loser : (p p' : Player) → loses p → loses p' → p ≡ p'
  one-loser p p' p-l p'-l with p ≡? p'
  ... | yes p≡p' = p≡p'
  ... | no  p≢p' = ⊥-elim (<-irreflexive'' (bound p p' p≢p' p-l) (bound p' p (p≢p' ∘ sym) p'-l))

  incorrect-loses : (q : Player) → ¬ guessesCorrectly (assemble R q) c → loses q
  incorrect-loses q ¬gc with snd (rep≗* (lane q)) (succ (PlayerView.M q))
  ... | right ∈  = ∈
  ... | left  eq = ⊥-elim (¬gc goal)
    where
    open PlayerView q

    mostly-identical : mostly-our-lane ≗* lane q
    mostly-identical = insert-≗* (succ M) (lane q) dummy

    goal : rep mostly-our-lane (succ M) ≡ c (pack q (succ M))
    goal = trans (respects mostly-identical (succ M)) eq

  correct : (q q' : Player) → ¬ guessesCorrectly (assemble R q) c → ¬ guessesCorrectly (assemble R q') c → q ≡ q'
  correct q q' ¬gc-q ¬gc-q' =
    one-loser q q' (incorrect-loses q ¬gc-q) (incorrect-loses q' ¬gc-q')
```

TODO
cite Gabay–O'Connor and Hardin & Taylor
