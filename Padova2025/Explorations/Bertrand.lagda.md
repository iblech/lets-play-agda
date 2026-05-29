```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Explorations.Bertrand where
```

# Bertrand's postulate

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Connectives.More
open import Padova2025.ProvingBasics.Termination.Ordering
open import Padova2025.ProvingBasics.Termination.Gas
```

Bertrand's postulate is a basic result in number theory. It states
that for every positive natural number $n$, there is a prime number $p$
with $n < p ≤ 2n$. The [standard proof of this fact](https://en.wikipedia.org/wiki/Proof_of_Bertrand%27s_postulate)
proceeds in two steps: First, for the numbers $n ≥ 427$, an argument
involving binomial coefficients is given. Second, for the finitely
many numbers $n < 427$, the claim is just checked by brute force,
without specific mathematical insight.

In this module, we aim to formalize this second step in Agda, as it is
a refreshing change of pace from typical conceptual proofs. (A correct
but hard to read [full proof](https://github.com/Deducteam/matita_lib_in_agda/blob/master/matita-arithmetics-chebyshev-bertrand.agda)
was offered by Thiago Felicissimo and Frédéric Blanqui, as a [case
study in mechanically translating proofs in the impredicative Matita
system to predicative Agda](https://arxiv.org/abs/2308.15465).)
First, let's formalize the claim.


## Formalization of the claim

```
-- `a ∣ b` expresses that `a` divides `b`.
_∣_ : ℕ → ℕ → Set
a ∣ b = b % a ≡ zero
-- An alternative (and perhaps better) formulation would be:
-- dec-∣ a b = Σ[ k ∈ ℕ ] b ≡ k · a

-- `IsPrime p` expresses that `p` is a prime number.
IsPrime : ℕ → Set
IsPrime p = p ≥ two × All (λ k → k > zero → k ∣ p → k ≡ one) (downFrom p)

-- `BertrandClaim n` expresses that there is a prime number which is
-- more than `n` and at most `2 · n` (or alternatively that `n` is zero).
BertrandClaim : ℕ → Set
BertrandClaim n = n ≡ zero ⊎ ∃[ p ] n < p × p ≤ twice n × IsPrime p
```


## Decision procedures and partial decision procedures

A value of type `Dec X` decides `X` in the sense of either supplying an
inhabitant of `X` or supplying a witness that no such inhabitant exists.
Divisibility, primality, the existence of a prime below a given upper bound:
these are all decidable. But in the following, we sometimes settle
for *partial decision procedures*, functions which either
return a witness or leave the matter undecided. We do this both
to cut down on the number of proof obligations and for fun,
to explore this approximative version of decidability.

```
dec-∣ : (a b : ℕ) → Dec (a ∣ b)
-- Holify
dec-∣ a b = b % a ≟ zero
```

```
dec-trivial-divisor : (p k : ℕ) → Dec (k > zero → k ∣ p → k ≡ one)
-- Holify
dec-trivial-divisor p k = dec-→ (dec-< zero k) (dec-→ (dec-∣ k p) (k ≟ one))
```

```
prime? : (p : ℕ) → Maybe (IsPrime p)
prime? p with dec-≤ two p | dec-All (dec-trivial-divisor p) (downFrom p)
... | yes two≤p | yes f = {--}just (two≤p , f){--}
... | _         | _     = {--}nothing{--}
```

```
bertrand₀? : (n p : ℕ) → Maybe (n < p × p ≤ twice n × IsPrime p)
bertrand₀? n p with dec-< n p | dec-≤ p (twice n) | prime? p
... | yes n<p | yes p≤2n | just f = {--}just (n<p , p≤2n , f){--}
... | _       | _        | _      = {--}nothing{--}
```

The following function is the analogue of [`find` from
Padova2025.ProvingBasics.Connectives.More](Padova2025.ProvingBasics.Connectives.More.html#find)
for partial decidability instead of full decidability.

```
find' : {A : Set} {P : A → Set} → ((x : A) → Maybe (P x)) → (xs : List A) → Maybe (Any P xs)
-- Holify
find' P? [] = nothing
find' P? (x ∷ xs) with P? x | find' P? xs
... | just px  | _       = just (here px)
... | nothing  | just q  = just (there q)
... | nothing  | nothing = nothing
```

```
bertrand? : (n : ℕ) → Maybe (BertrandClaim n)
bertrand? n with n ≟ zero | find' (bertrand₀? n) (downFrom (succ (twice n)))
... | yes n≡zero | _       = {--}just (left n≡zero){--}
... | no  n≢zero | just f  = {--}just (right (satisfied f)){--}
... | no  n≢zero | nothing = {--}nothing{--}
```


## Empirically observing the claim

We would like to prove the following result.

```code
claim : (n : ℕ) → n < 427 → BertrandClaim n
```

The function `bertrand?` computes for an arbitrary input `n` a value
of type `Maybe (BertrandClaim n)`, and -- by Bertrand's postulate --
these values will in fact all be of the form `just _`. Agda can verify
this fact for each particular number `n`, by blithely evaluating
`bertrand? n`, but we can neither strip away the `just` constructor in
the general case of a variable `n : ℕ`.

To proceed, we first collect all the positive verdicts of the partical
decision procedure for the first 427 numbers into an `All` structure.

```
claim? : Maybe (All BertrandClaim (downFrom ten))
claim? = collect bertrand? ten
-- We should really put 427 here, but use 10 to reduce the load on the Let's play Agda server.
```

We don't supply a reason that `claim?` is of the form `just _`.
But it is, and Agda will verify this single fact when
we put `claim?` in the following hole:

```
empirical-fact : All BertrandClaim (downFrom ten)
empirical-fact = from-just {--}claim?{--}
```

We can then use this structure to prove the claim.

```
claim : (n : ℕ) → n < ten → BertrandClaim n
claim n n<10 = lookup empirical-fact n<10
```

To explore this further, put your favorite number below ten
into the hole below and then press `C-c C-v` to run `example`,
obtaining a printout of a prime number which is more than your
number and at most twice your number.

```
fav : ℕ
fav = {--}four{--}

example : BertrandClaim fav
example = claim fav fav<ten
  where
  fav<ten = {--}from-just (Dec→Maybe (dec-< fav ten)){--}
```
