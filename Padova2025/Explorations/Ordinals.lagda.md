```
module Padova2025.Explorations.Ordinals where
```

# Numbers larger than infinity

```
open import Padova2025.ProgrammingBasics.Naturals.Base
```

::: Todo :::
Rough sketch, bring into shape. And add lots of praise for
https://arxiv.org/abs/2208.03844 which this account is based on.
:::

    0, 1, 2, 3, 4, ..., ω, ω + 1, ω + 2, ...,
    ^^^^^^^^^^^^^^^^^^  ^
     these are natural   ∞ is not a nat. numb.
	 numbers

    ω + ω = ω·2, ..., ω·3, ..., ω·ω = ω², ..., ω³, ...,

    ω^ω, ..., ω^(ω·2), ..., ω^(ω^ω), ..., ω^(ω^(ω^ω)), ...,

    ω^(ω^(ω^…)) = ε₀, ε₀ + 1, ..., ε₀·2, ...,

    ε₀^(ε₀^(ε₀^…)) = ε₁, ..., ε₂, ..., ε_ω, ..., ε_{ω+1}, ...,

    ε_{ε₀}, ..., ε_{ε₁}, ..., ε_{ε₂}, ..., ε_{ε_{ε_…}} = ζ₀, ...

    This is the beginning of the list of ordinal numbers.
    The displayed numbers are still tiny in the sense that
    each number has only countably many predeccesors.

    Picture of ω:
      :-)   I  I  I  I  I  ...
      
    Picture of ω + 1:
	   +------------------+ 
      :-)  |I  I  I  I  I  ...|  I
	   +------------------+
	  
    Picture of ω + ω + 1:
	   +-------------+  +-------------+
      :-)  |I  I  I  ... |  |I  I  I  ... |  I
	   +-------------+  +-------------+

    Picture of 1 + ω:
      :-)   I  I  I  I  I  I  ...

    What do we know about ω + 1 vs. 1 + ω?
    A: succ ω = ω + 1 > ω;   1 + ω = ω.

The three fundamental convictions regarding (countable)
ordinals numbers are:

1. Zero should exist.
2. Every number should have a successor.
3. Every (strictly ascending) sequence should have a limit.

For instance, ω is the limit of the sequence

      0,   1,   2,  3, ...
      ||   ||   ||
      f 0  f 1  f 2

Note: ω is also the limit of the sequence

      0,   1,   2,   4,   8,  16,  32, ...
      ||   ||   ||   ||   ||
      g 0  g 1  g 2  g 3  g 4

We simultaneously define, in a mutual manner, a type `O` of (representations
of) ordinal numbers, types `x < y` of witnesses that `x` is strictly smaller
than `y`, types `x ≤ y` of witnesses that `x` is at most `y`, and for each
function `f : ℕ → O` a type `Monotonic f` of witnesses that `f` is a strictly
increasing sequence.

```
infix 4 _≤_ _<_
data O : Set
data _≤_ : O → O → Set
_<_ : O → O → Set
Monotonic : (ℕ → O) → Set
```

```
Monotonic f = (n : ℕ) → f n < f (succ n)

data O where
  zer : O
  suc : O → O
  lim : (f : ℕ → O) → Monotonic f → O

x < y = suc x ≤ y

data _≤_ where
  ≤-zer      : {x : O} → zer ≤ x
  ≤-suc-mon  : {x y : O} → x ≤ y → suc x ≤ suc y
  ≤-trans    : {x y z : O} → x ≤ y → y ≤ z → x ≤ z
  ≤-cocone   : {f : ℕ → O} {fmon : Monotonic f} {x : O} {n : ℕ}
             → x ≤ f n → x ≤ lim f fmon
  ≤-limiting : {f : ℕ → O} {fmon : Monotonic f} {x : O}
             → ((n : ℕ) → f n ≤ x) → lim f fmon ≤ x
```


## Exercise: Basic properties

If the terms of `f` are all at most the corresponding term in `g`,
then the limit of `f` is at most the limit of `g`.

```
lim-mon
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → ((n : ℕ) → f n ≤ g n)
  → lim f fmon ≤ lim g gmon
-- Holify
lim-mon p = ≤-limiting (λ n → ≤-cocone (p n))
```

```
≤-refl : {x : O} → x ≤ x
-- Holify
≤-refl {zer}        = ≤-zer
≤-refl {suc x}      = ≤-suc-mon ≤-refl
≤-refl {lim f fmon} = lim-mon (λ a → ≤-refl)
```

```
id≤suc : {x : O} → x ≤ suc x
-- Holify
id≤suc {zer}     = ≤-zer
id≤suc {suc x}   = ≤-suc-mon id≤suc
id≤suc {lim f x} = ≤-limiting (λ n → ≤-trans id≤suc (≤-suc-mon (≤-cocone ≤-refl)))
```


## Exercise: Defining infinity

```
fromℕ : ℕ → O
fromℕ zero     = zer
fromℕ (succ n) = suc (fromℕ n)
```

```
fromℕ-mon : Monotonic fromℕ
-- Holify
fromℕ-mon n = ≤-refl
```

```
uno : O
uno = suc zer
```

```
ω : O
ω = lim fromℕ fromℕ-mon
```

```
ω' : O
ω' = lim (λ n → fromℕ (succ n)) {--}(λ n → ≤-refl){--}
```

```
example₀ : ω ≤ ω'
-- Holify
example₀ = lim-mon (λ n → id≤suc)
```

```
example₁ : ω' ≤ ω
-- Holify
example₁ = ≤-limiting (λ n → ≤-cocone {n = succ n} ≤-refl)
```


## Ordinal addition

In a mutual manner, we simultaneously define ordinal addition and prove a
monotonicity result for ordinal addition.

```
infixl 6 _+_
_+_ : O → O → O
+-mon : {x a b : O} → a ≤ b → (x + a) ≤ (x + b)
```

Here is the definition of ordinal addition.

```
a + zer        = a
a + suc b      = suc (a + b)
a + lim f fmon = lim (λ n → a + f n) (λ n → +-mon (fmon n))
```

Now you are asked to fill in the required lemma.

```
+-mon {b = zer} ≤-zer        = {--}≤-refl{--}
+-mon {b = suc b} ≤-zer      = {--}≤-trans id≤suc (≤-suc-mon (+-mon ≤-zer)){--}
+-mon {b = lim f fmon} ≤-zer = {--}≤-cocone (+-mon (≤-zer {f zero})){--}
+-mon (≤-trans p q)          = {--}≤-trans (+-mon p) (+-mon q){--}
+-mon (≤-suc-mon p)          = {--}≤-suc-mon (+-mon p){--}
+-mon (≤-cocone p)           = {--}≤-cocone (+-mon p){--}
+-mon (≤-limiting p)         = {--}≤-limiting (λ b → +-mon (p b)){--}
```


## Exercise: Infinity plus one and one plus infinity

```
example₂ : ω < ω + uno
-- Holify
example₂ = ≤-refl
```

```
example₃ : uno + ω ≤ ω
-- Holify
example₃ = ≤-limiting (λ n → ≤-cocone {n = succ n} (lemma n))
  where
  lemma : (n : ℕ) → (suc zer + fromℕ n) ≤ suc (fromℕ n)
  lemma zero     = ≤-refl
  lemma (succ n) = ≤-suc-mon (lemma n)
```


## Exercise: Adding zero

```
+-zer : (x : O) → zer + x ≤ x
-- Holify
+-zer zer       = ≤-zer
+-zer (suc x)   = ≤-suc-mon (+-zer x)
+-zer (lim f x) = lim-mon (λ n → +-zer (f n))
```


## Outlook

Beyond these first steps with ordinals, the following projects might be interesting.

- Defining ordinal multiplication and exponentiation, by
  implementing the rules listed on the Wikipedia page on ordinal arithmetic
- Defining the ordinal number `ε₀`
- Stating and proving that `ω ^ ε₀` is the same as `ε₀`
- Defining the numbers `ε₁`, `ε₂`, ...

Do not expect these exercises to have short solutions---the
monotonicity requirement in the `lim` constructor entails
quite a few proof obligations. However, we cannot drop this
requirement as else exponentiation is no longer definable:
The definition requires a case distinction which is possible
only because of the monotonicity requirement.

An extensive discussion is included in the following landmark papers
by Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu:

- [Type-Theoretic Approaches to Ordinals](https://arxiv.org/abs/2208.03844)
- [Set-Theoretic and Type-Theoretic Ordinals Coincide](https://arxiv.org/abs/2301.10696)
- [Ordinal Exponentiation in Homotopy Type Theory](https://arxiv.org/abs/2501.14542)
