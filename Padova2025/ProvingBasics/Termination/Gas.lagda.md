```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Termination.Gas where
```

# Gas

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Equality.Base
```

To be convinced that a recursion eventually terminates, Agda's termination
checker needs to observe that the recursive call is on *structurally smaller*
arguments, such as `x` being structurally smaller than `succ x`. Custom
ordering relations, no matter how relevant to the situation at hand, are not
consulted by Agda's termination checker.

To satisfy the termination checker, we can introduce an additional
argument whose only purpose is to get structurally smaller at each step.

```
digits₃ : ℕ → ℕ
digits₃ x = go (succ x) x
  where
  go : (gas : ℕ) → (x : ℕ) → ℕ
  go zero       x          = zero  -- bailout, give up, should never be reached
  go (succ gas) zero       = zero
  go (succ gas) x@(succ _) = succ (go gas (half x))
```

This definition works because an initial gas of `succ x` is always sufficient to
compute the correct answer. (Using `x` as initial gas would also work, but only
because we put `zero` in the bailout case.)

However, the proof that `digits₃ x ≡ succ (digits₃ (half x))` for positive `x`
is a bit involved (and therefore here *not* suggested as an exercise).

```code
digits₃-eq : (x : ℕ) → digits₃ (succ x) ≡ succ (digits₃ (half (succ x)))
digits₃-eq x = {!!}
```

A much better way is provided by the [more sophisticated kind of
gas](Padova2025.ProvingBasics.Termination.WellFounded.html) discussed in
the next module.


## Tagging the exceptional case

We were able to imagine some (arbitrary) definition in the bailout case above,
because the codomain `ℕ` is inhabited. In other cases, for instance when the
codomain is some type of witnesses, no suitable "error value" might be at hand.
To make the gas method work, we then use a more explicit mechanism for
signaling the bailout case.

```
data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A
```

```
digits₃' : ℕ → Maybe ℕ
digits₃' x = go (succ x) x
  where
  go : (gas : ℕ) → (x : ℕ) → Maybe ℕ
  go zero       x          = nothing  -- bailout
  go (succ gas) zero       = just zero
  go (succ gas) x@(succ _) with go gas (half x)
  ... | nothing = nothing
  ... | just y  = just (succ y)
```

In this version, the original simple structure of the recursive call (`succ
(digits (half x))`) has been lost; we can try to recover it by using the
`_>>=_` operator.

```
infixl 1 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just x  >>= f = f x
```

```
digits₃'' : ℕ → Maybe ℕ
digits₃'' x = go (succ x) x
  where
  go : (gas : ℕ) → (x : ℕ) → Maybe ℕ
  go zero       x          = nothing  -- bailout
  go (succ gas) zero       = just zero
  go (succ gas) x@(succ _) = go gas (half x) >>= λ y → just (succ y)
```

Employing so-called [do notation](https://agda.readthedocs.io/en/stable/language/syntactic-sugar.html#do-notation),
we can improve the presentation a bit more:

```
digits₃''' : ℕ → Maybe ℕ
digits₃''' x = go (succ x) x
  where
  go : (gas : ℕ) → (x : ℕ) → Maybe ℕ
  go zero       x          = nothing  -- bailout
  go (succ gas) zero       = just zero
  go (succ gas) x@(succ _) = do
    y ← go gas (half x)
    just (succ y)
```

However, proofs involving any of these versions of `digits₃` are still quite
intricate, and also not particularly insightful. As an exercise, you could try
proving that `digits₃' x` is of the form `just _` for every number `x`.


### Other applications of `Maybe`

The expression `lookupMaybe xs n` should reduce to (`just` of) element
nr. `n` of the list `xs` if such an element exists, and to `nothing`
otherwise.

```
lookupMaybe : {X : Set} → List X → ℕ → Maybe X
-- Holify
lookupMaybe []       n        = nothing
lookupMaybe (x ∷ xs) zero     = just x
lookupMaybe (x ∷ xs) (succ n) = lookupMaybe xs n

-- Tests
-- EX: lookupMaybe (four ∷ two ∷ one ∷ []) one   ≡ just two
-- EX: lookupMaybe (four ∷ two ∷ one ∷ []) two   ≡ just one
-- EX: lookupMaybe (four ∷ two ∷ one ∷ []) three ≡ nothing
```


### Injectivity of the constructor

```
just-injective : {X : Set} {a b : X} → just a ≡ just b → a ≡ b
-- Holify
just-injective refl = refl
```


## Prooflessly extracting results in concrete instances

Without having to prove that the results of `digits₃'` are always of the form
`just _`, we can still extract the results in concrete instances. For instance,
to obtain `digits₃' five` as an actual element of `ℕ` (instead of `Maybe ℕ`),
we can carry out the following preparations...

```
record 𝟙 : Set where
  constructor tt

module _ {A : Set} where
  From-just : Maybe A → Set
  From-just nothing  = 𝟙
  From-just (just _) = A

  from-just : (m : Maybe A) → From-just m
  from-just nothing  = tt
  from-just (just x) = x
```

...and then obtain the value as follows.

```
example-digits-computation : ℕ
-- Holify
example-digits-computation = from-just (digits₃' five)

-- Tests
-- EX: example-digits-computation ≡ three
```

Put `from-just (digits₃' five)` in the hole;
then observe, using `C-c C-v`, that `example-digits-computation` is `three`.


## Exercise: Division and modulo

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Termination.Ordering
```

The following snippet of code is intended to implement division, but
fails to satisfy the termination checker (and indeed, does not
terminate in case the divisor is zero).

```
infix 7 _/_
```

```code
_/_ : ℕ → ℕ → ℕ
a / b with ≤-<-connex b a
... | left  b≤a = succ ((a ∸ b) / b)
... | right a<b = zero
```

Use the brittle gas technique introduced in this module to provide a
terminating and correct version of division. You do not need to verify
that your implementation is indeed correct. In case the divisor is zero,
your function may compute whatever you like.

```
_/_ : ℕ → ℕ → ℕ
-- Holify
_/_ a b = go a a
  where
  go : (gas : ℕ) → (x : ℕ) → ℕ
  go zero       x = zero  -- bailout
  go (succ gas) x with ≤-<-connex b x
  ... | left  b≤x = succ (go gas (x ∸ b))
  ... | right x<b = zero

-- Tests
-- EX: two   / one   ≡ two
-- EX: two   / two   ≡ one
-- EX: two   / three ≡ zero
-- EX: two   / four  ≡ zero
-- EX: two   / five  ≡ zero
-- EX: three / one   ≡ three
-- EX: three / two   ≡ one
-- EX: three / three ≡ one
-- EX: three / four  ≡ zero
-- EX: three / five  ≡ zero
-- EX: four  / one   ≡ four
-- EX: four  / two   ≡ two
-- EX: four  / three ≡ one
-- EX: four  / four  ≡ one
-- EX: four  / five  ≡ zero
-- EX: five  / one   ≡ five
-- EX: five  / two   ≡ two
-- EX: five  / three ≡ one
-- EX: five  / four  ≡ one
-- EX: five  / five  ≡ one
```

Similarly, the following code is supposed to implement the modulo
operation, but fails the termination checker; provide a terminating
version.

```
infix 7 _%_
```

```code
_%_ : ℕ → ℕ → ℕ
a % b with ≤-<-connex b a
... | left  b≤a = (a ∸ b) % b
... | right a<b = a
```

```
_%_ : ℕ → ℕ → ℕ
-- Holify
_%_ a b = go a a
  where
  go : (gas : ℕ) → (x : ℕ) → ℕ
  go zero       x = zero  -- bailout
  go (succ gas) x with ≤-<-connex b x
  ... | left  b≤x = go gas (x ∸ b)
  ... | right x<b = x

-- Tests
-- EX: two   % one   ≡ zero
-- EX: two   % two   ≡ zero
-- EX: two   % three ≡ two
-- EX: two   % four  ≡ two
-- EX: two   % five  ≡ two
-- EX: three % one   ≡ zero
-- EX: three % two   ≡ one
-- EX: three % three ≡ zero
-- EX: three % four  ≡ three
-- EX: three % five  ≡ three
-- EX: four  % one   ≡ zero
-- EX: four  % two   ≡ zero
-- EX: four  % three ≡ one
-- EX: four  % four  ≡ zero
-- EX: four  % five  ≡ four
-- EX: five  % one   ≡ zero
-- EX: five  % two   ≡ one
-- EX: five  % three ≡ two
-- EX: five  % four  ≡ one
-- EX: five  % five  ≡ zero
```
