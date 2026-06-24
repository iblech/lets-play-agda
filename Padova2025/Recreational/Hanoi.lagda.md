```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Recreational.Hanoi where
```

# The Tower of Hanoi

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Vectors
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.More using (Dec; yes; no)
```

A finite number of disks is stacked on a peg `A`. They should be moved to a
different peg `C`. Temporarily, disks may also be parked on a third peg `B`.
The catch: The disks each have a different size, and at no point may a larger
disk rest on a smaller one.

[This celebrated puzzle has a well-known recursive solution.](https://en.wikipedia.org/wiki/Tower_of_Hanoi)
To move $n$ disks from peg `A` to `C`, do the following:

1. Recursively move the topmost $n - 1$ disks from `A` to the auxiliary peg `B`.
   The disk which was originally the $n$-th disk on `A` is now at the top.
2. Move that disk from `A` to the target peg `C`.
3. Recursively move the $n - 1$ disks from peg `B` to `C`.

Let us formalize the puzzle and this solution in Agda. With just a tiny
adaptation of this strategy, we will even be able to prove that any valid
configuration of disks can be reached from any other valid configuration by a
valid sequence of moves, and we can run this proof to determine such a valid
sequence of moves.

We will follow a correct-by-construction approach, so the description of the
strategy and the proof that the strategy is indeed working as it should are
unified into a single artefact.


## Preliminaries

For a vector `xs` and a predicate `P`, the type `All P xs` expresses that every
element of the vector `xs` satisfies `P`. An inhabitant of `All P xs` is a list
of suitable witnesses.
The following definition is lifted straight from
[Padova2025.ProvingBasics.Connectives.More](Padova2025.ProvingBasics.Connectives.More.html#All),
where we discussed the same notion but for lists instead of vectors.

```
data All {A : Set} (P : A → Set) : {n : ℕ} → Vector A n → Set where
  []  : All P []
  _∷_ : {n : ℕ} {x : A} {xs : Vector A n} → P x → All P xs → All P (x ∷ xs)
```

```
all-replicateV : {n : ℕ} {A : Set} {P : A → Set} {x : A} → P x → All P (replicateV n x)
all-replicateV {zero}   px = {--}[]{--}
all-replicateV {succ n} px = {--}px ∷ all-replicateV px{--}
```


## Formalization of the puzzle

The three pegs are encoded by the following type with three constructors.

```
data Peg : Set where
  A : Peg
  B : Peg
  C : Peg
```

A configuration of $n$ disks is a vector of pegs of length $n$, with the $i$-th
entry telling us on which peg the $i$-th disk is placed. We don't need to
record the disk's position within its peg, as it is uniquely determined by the
size requirement anyway. (But we will need to impose a size-related restriction
when formalizing the notion of a valid move.)

```
Config : ℕ → Set
Config n = Vector Peg n
```

A (valid) game move either relocates the largest disk from its peg to another,
or leaves it untouched and is hence a (valid) move in the subgame with the
largest disk imagined away. In the first case, for the move to be valid, all
smaller disks need to sit on neither the source peg (else the largest disk is
not exposed) nor the target peg (else the largest disk cannot be put there).

The type `Move c c'` is the type of (valid) moves from configuration `c` to
configuration `c'`.

```
data Move : {n : ℕ} → Config n → Config n → Set where
  here
    : {n : ℕ}
    → (source target : Peg) {c : Config n}
    → source ≢ target → All (λ p → p ≢ source × p ≢ target) c
    → Move (source ∷ c) (target ∷ c)
  there
    : {n : ℕ} {c c' : Config n} {p : Peg}
    → Move c c'
    → Move (p ∷ c) (p ∷ c')
```

A (valid) play is a sequence of (valid) moves. We track the starting and ending
configuration directly in the type signature.

```
infixr 5 _◅_
data Star {X : Set} (P : X → X → Set) : X → X → Set where
  ε   : {x : X} → Star P x x
  _◅_ : {a b c : X} → (x : P a b) → (xs : Star P b c) → Star P a c
```

```
Play : {n : ℕ} → Config n → Config n → Set
Play = Star Move
```


## Auxiliary results

Equality of pegs is decidable, by the following boring proof where we just
visit every case.

```
_≡?_ : (p p' : Peg) → Dec (p ≡ p')
A ≡? A = yes refl
A ≡? B = no λ ()
A ≡? C = no λ ()
B ≡? A = no λ ()
B ≡? B = yes refl
B ≡? C = no λ ()
C ≡? A = no λ ()
C ≡? B = no λ ()
C ≡? C = yes refl
```

We can concatenate sequences of moves.

```
infixr 5 _◅◅_
_◅◅_ : {X : Set} {P : X → X → Set} {a b c : X} → Star P a b → Star P b c → Star P a c
-- Holify
_◅◅_ ε        ys = ys
_◅◅_ (x ◅ xs) ys = x ◅ (xs ◅◅ ys)
```

We can translate a play in the $n$-disk subgame without the largest disk to a
play in the full $(n + 1)$-disk game. We call this operation `frame` in
reference to the frame rule of [separation logic](https://en.wikipedia.org/wiki/Separation_logic),
which likewise lets one lift a statement about a small part of the system to
the whole, leaving everything else untouched.

```
frame : {n : ℕ} (p : Peg) {c c' : Config n} → Play c c' → Play (p ∷ c) (p ∷ c')
-- Holify
frame p ε        = ε
frame p (m ◅ ms) = there m ◅ frame p ms
```

There is always a third peg.

```
third : (p p' : Peg) → p ≢ p' → Σ[ q ∈ Peg ] q ≢ p × q ≢ p'
-- Holify
third A A p≢p' = ⊥-elim (p≢p' refl)
third A B p≢p' = C , (λ ()) , (λ ())
third A C p≢p' = B , (λ ()) , (λ ())
third B A p≢p' = C , (λ ()) , (λ ())
third B B p≢p' = ⊥-elim (p≢p' refl)
third B C p≢p' = A , (λ ()) , (λ ())
third C A p≢p' = B , (λ ()) , (λ ())
third C B p≢p' = A , (λ ()) , (λ ())
third C C p≢p' = ⊥-elim (p≢p' refl)
```


## Formalization of the solution

Given distinct pegs `source`, `target` and `auxiliary`, the following
function produces a play which, starting from the configuration that all disks
are on `source`, moves them to `target`. No separate correctness proof is
needed -- correctness is already established by the types.
(The strategy outlined in the comments is optimal, though this is neither
stated nor proven.)

```
solve₀
  : {n : ℕ} → (source target auxiliary : Peg)
  → source ≢ target
  → source ≢ auxiliary
  → target ≢ auxiliary
  → Play (replicateV n source) (replicateV n target)
solve₀ {zero}   source target auxiliary s≢t s≢a t≢a = {--}ε{--}
solve₀ {succ n} source target auxiliary s≢t s≢a t≢a =
  -- Step 1: Move the topmost n disks to the auxiliary peg.
  {--}frame source (solve₀ source auxiliary target s≢a s≢t a≢t){--} ◅◅
  -- Step 2: Move the now-exposed disk to the target peg.
  {--}here source target s≢t (all-replicateV (a≢s , a≢t)){--} ◅
  -- Step 3: Move the n disks from their temporary parking position to the target peg.
  {--}frame target (solve₀ auxiliary target source a≢t a≢s t≢s){--}
  where
  a≢t = ≢-sym t≢a
  a≢s = ≢-sym s≢a
  t≢s = ≢-sym s≢t
```

With just a bit more work, we can show that every (valid) configuration is
reachable from any other:

```
solve : {n : ℕ} → (c c' : Config n) → Play c c'
solve []      []        = {--}ε{--}
solve (p ∷ c) (p' ∷ c') with p ≡? p'
... | yes refl = {--}frame p (solve c c'){--}
... | no  p≢p' =
  let (q , q≢p,p') = third p p' p≢p'
      mid          = replicateV _ q
  in
  -- Step 1: Move the topmost n disks to the auxiliary peg.
  {--}frame p (solve c mid){--} ◅◅
  -- Step 2: Move the now-exposed (n + 1)-th disk to where it belongs.
  {--}here p p' p≢p' (all-replicateV q≢p,p'){--} ◅
  -- Step 3: Move the parked disks to where they belong.
  {--}frame p' (solve mid c'){--}
```

Again, correctness is ensured by the types. (But unlike `solve₀`, the function
`solve` does not always compute optimal plays.)

Time to run our proofs! Put, for instance, `replicateV three A` and `replicateV
three C` in the two holes in the type signature and `solve _ _` into the
remaining hole below. Then use `C-c C-v` to run `example` and observe the
resulting sequence of moves. (The output will be a bit littered by inequality
witnesses.)

```
example : Play {--}(replicateV three A){--} {--}(replicateV three C){--}
example = {--}solve _ _{--}
```

<!--
## Pretty-printing plays

Enjoy running `solve₀` or `solve` (using `C-c C-v`), to obtain suitable
sequences of moves. The output will contain inequality witnesses, which are
important for the proofs but not relevant for the mere algorithmic question of
which disks to move where.

```code
open import Padova2025.ProgrammingBasics.Lists
```

```code
toList : {n : ℕ} {c c' : Config n} → Play c c' → List (Peg × Peg)
toList ε        = []
toList (m ◅ ms) = go m ∷ toList ms
  where
  go : {n : ℕ} {c c' : Config n} → Move c c' → Peg × Peg
  go (here source target _ _) = source , target
  go (there m)                = go m
```

```code
example : List (Peg × Peg)
example = toList (solve (replicateV three A) (replicateV three C))
```

```code
_ : example ≡ (A , C) ∷ (A , B) ∷ (C , B) ∷ (A , C) ∷ (B , A) ∷ (B , C) ∷ (A , C) ∷ []
_ = refl
```
-->
