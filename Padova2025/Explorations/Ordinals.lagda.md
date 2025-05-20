```
module Padova2025.Explorations.Ordinals where
```

# Numbers larger than infinity

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Termination.Gas using (𝟙; tt)
```

::: Todo :::
Rough sketch, bring into shape. And add lots of praise for
https://arxiv.org/abs/2208.03844 which this account is based on.
:::

A key motto in set theory is: *Never stop, always continue.* This motto is
nicely exemplified by the *ordinal numbers*, one of several flavors of numbering
systems which support infinitely large numbers (other prominent flavors are the
cardinal numbers and the surreal numbers).

The ordinal numbers start like this:

> 0, 1, 2, 3, 4, ...

However, unlike the natural numbers, we then don't stop. Instead we continue:

> 0, 1, 2, 3, 4, …, ω

So ω is the first infinite number. But it is not the last one, as we
continue:

> 0, 1, 2, 3, 4, …, ω, ω + 1, ω + 2, …

Should there be a number larger than all of those? Following the motto, of
course there should:

> 0, 1, 2, 3, 4, …, ω, ω + 1, ω + 2, ..., ω + ω = ω · 2

Now increasing our cruise speed and skipping over infinitely many numbers, we
eventually obtain the following creatures:

> ω · ω = ω², ω³, ω⁴, ω<sup>ω</sup>, ω<sup><sup>ω</sup></sup>,
> ω<sup>ω<sup>ω<sup>⋰</sup></sup></sup> = ε₀,
> ε₀<sup>ε₀<sup>ε₀<sup>⋰</sup></sup></sup> = ε₁,
> ε₁<sup>ε₁<sup>ε₁<sup>⋰</sup></sup></sup> = ε₂

In this way we obtain more and more *epsilon numbers*. After having obtained
ε₀, ε₁, ε₂ and so on we keep going to obtain ε<sub>ω</sub>, ε<sub>ε₀</sub>,
ε<sub>ε<sub>ε₀</sub></sub>, and so on; still not stopping, we eventually obtain the
number

> ε<sub>ε<sub>ε<sub>⋱</sub></sub></sub> = ζ₀

and still have a long way to go. Armed with just the operations "add one" and
"keep going", starting with zero we have thereby obtained quite a few numbers.
(Which, by the way, are still considered puny by seasoned set theorists: All
the displayed numbers have only countably many predecessors.)

For a tour of a longer initial segment of the ordinals, we recommend
[an account by John Baez ](https://johncarlosbaez.wordpress.com/2016/06/29/large-countable-ordinals-part-1/).

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

We will see below that the `≤-trans` constructor is not needed,
however the proof is not particularly short.


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
  lemma : (n : ℕ) → suc zer + fromℕ n ≤ suc (fromℕ n)
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


## Exercise: A more general comparison lemma

The type `f simulates g` defined below contains witnesses of the
assertion that every term in the sequence `g` is dominated by some
term in the sequence `f`. For instance, the sequence `0, 1, 2, …`
simulates the sequence `0, 1, 2, 4, 8, 16, …` (and vice versa).

```
_simulates_ : (ℕ → O) → (ℕ → O) → Set
f simulates g = (a : ℕ) → ∃[ b ] g a ≤ f b
```

```
comparison-lemma
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → f simulates g → lim g gmon ≤ lim f fmon
-- Holify
comparison-lemma sim = ≤-limiting (λ n → ≤-cocone (snd (sim n)))
```

With this comparison lemma in place, we can reprove `lim-mon` from above:

```
lim-mon'
  : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g}
  → ((n : ℕ) → f n ≤ g n)
  → lim f fmon ≤ lim g gmon
lim-mon' p = comparison-lemma {--}(λ n → n , p n){--}
```


## Exercise: Equality of ordinal numbers

The elements of type `O` are not ordinal numbers, but (mostly
non-unique) representations of ordinal numbers. Hence for many
purposes a custom equivalence relation is more appropriate than the
standard equality type of `O`:

```
infix 4 _≈_
_≈_ : O → O → Set
x ≈ y = x ≤ y × y ≤ x
```


## Exercise: A direct description of inequality

Above, we have defined `_≤_` in an inductive fashion. This makes it
easy to construct witnesses, but hard to assess whether for given
ordinal number (representations) `x` and `y` a witness of type `x ≤ y`
exists. For this task, a direct description is more useful.

```
Code : O → O → Set
Code zer          y            = 𝟙
Code (suc x)      zer          = ⊥
Code (suc x)      (suc y)      = Code x y
Code (suc x)      (lim f fmon) = ∃[ n ] Code (suc x) (f n)
Code (lim f fmon) zer          = ⊥
Code (lim f fmon) (suc y)      = (k : ℕ) → Code (f k) (suc y)
Code (lim f fmon) (lim g gmon) = (k : ℕ) → ∃[ n ] Code (f k) (g n)
```

```
Code-refl : {x : O} → Code x x
-- Holify
Code-refl {zer}        = tt
Code-refl {suc x}      = Code-refl {x}
Code-refl {lim f fmon} = λ k → k , Code-refl {f k}
```

```
Code-suc : {x y : O} → Code x y → Code (suc x) (suc y)
-- Holify
Code-suc p = p
```

The following three auxiliary functions need to be defined
mutually. None of the following definitions is particularly pretty. We
need to power through.

```
Code-trans         : {x y z : O} → Code x y → Code y z → Code x z
Code-cocone        : {f : ℕ → O} {fmon : Monotonic f} {x : O} {n : ℕ} → Code x (f n) → Code x (lim f fmon)
Code-cocone-simple : {f : ℕ → O} {fmon : Monotonic f} {n : ℕ} → Code (f n) (lim f fmon)
```

```
Code-trans {zer}        {y}          {z}          p q       = {--}tt{--}
Code-trans {suc x}      {suc y}      {suc z}      p q       = {--}Code-trans {x} {y} {z} p q{--}
Code-trans {suc x}      {suc y}      {lim f fmon} p (n , q) = {--}n , Code-trans {suc x} {suc y} {f n} p q{--}
Code-trans {suc x}      {lim f fmon} {suc z}      (n , p) q = {--}Code-trans {suc x} {f n} {suc z} p (q n){--}
Code-trans {suc x}      {lim f fmon} {lim g gmon} (n , p) q = {--}fst (q n) , Code-trans {suc x} {f n} {g (fst (q n))} p (snd (q n)){--}
Code-trans {lim f fmon} {suc y}      {suc z}      p q       = {--}λ k → Code-trans {f k} {suc y} {suc z} (p k) q{--}
Code-trans {lim f fmon} {suc y}      {lim g gmon} p (n , q) = {--}λ k → n , Code-trans {f k} {suc y} {g n} (p k) q{--}
Code-trans {lim f fmon} {lim g gmon} {suc z}      p q       = {--}λ k → Code-trans {f k} {g (fst (p k))} {suc z} (snd (p k)) (q (fst (p k))){--}
Code-trans {lim f fmon} {lim g gmon} {lim h hmon} p q       = {--}λ k → fst (q (fst (p k))) , Code-trans {f k} (snd (p k)) (snd (q _)){--}
```

```
Code-cocone {x = zer}                p = {--}tt{--}
Code-cocone {x = suc x}              p = {--}_ , p{--}
Code-cocone {x = lim f fmon} {n = n} p = {--}λ k → n , Code-trans {x = f k} (Code-cocone-simple {f} {fmon} {k}) p{--}
```

```
Code-cocone-simple {f} {fmon} {n} = Code-cocone {f} {fmon} {f n} (Code-refl {f n})
```

```
Code-suc-inc-simple : {x : O} → Code x (suc x)
Code-suc-inc-simple {zer}        = {--}tt{--}
Code-suc-inc-simple {suc x}      = {--}Code-suc-inc-simple {x}{--}
Code-suc-inc-simple {lim f fmon} = {--}λ k → Code-trans {f k} {suc (f k)} {suc (lim f fmon)}
  (Code-suc-inc-simple {f k}) (Code-cocone-simple {f} {fmon} {k}){--}
```

```
toCode : {x y : O} → x ≤ y → Code x y
toCode ≤-zer = {--}tt{--}
toCode (≤-suc-mon p) = {--}toCode p{--}
toCode {x} (≤-trans p q) = {--}Code-trans {x} (toCode p) (toCode q){--}
toCode {x} (≤-cocone p) = {--}Code-cocone {x = x} (toCode p){--}
toCode {x} {zer} (≤-limiting {f} {fmon} p) = {--}Code-trans {suc (f zero)} {f one} (toCode (fmon zero)) (toCode (p one)){--}
toCode {x} {suc y} (≤-limiting {f} p) = {--}λ k → toCode {f k} {suc y} (p k){--}
toCode {x} {lim f fmon} (≤-limiting {g} {gmon} p) k with Code-trans {suc (g k)} {g (succ k)} (toCode (gmon k)) (toCode {g (succ k)} {lim f fmon} (p (succ k)))
... | (n , q) = {--}n , Code-trans {g k} {suc (g k)} (Code-suc-inc-simple {g k}) q{--}
```

```
fromCode : {x y : O} → Code x y → x ≤ y
fromCode {zer}        {y}          p       = {--}≤-zer{--}
fromCode {suc x}      {suc y}      p       = {--}≤-suc-mon (fromCode p){--}
fromCode {suc x}      {lim f fmon} (n , p) = {--}≤-cocone (fromCode p){--}
fromCode {lim f fmon} {suc y} p            = {--}≤-limiting λ n → fromCode (p n){--}
fromCode {lim f fmon} {lim g gmon} p       = {--}comparison-lemma (λ k → fst (p k) , fromCode (snd (p k))){--}
```

```
zer? : (x : O) → x ≈ zer ⊎ ¬ x ≈ zer
zer? zer          = {--}left  (≤-zer , ≤-zer){--}
zer? (suc x)      = {--}right λ p → toCode (fst p){--}
zer? (lim f fmon) = {--}right λ p → toCode (fst p){--}
```


## Multiplication with natural numbers and with ω

The purpose of this operation is to help get to `ε₀` with fewer proof
obligations than when properly setting up full multiplication.

```
infixl 7 _·ₙ_
_·ₙ_ : O → ℕ → O
x ·ₙ zero   = zer
x ·ₙ succ n = x ·ₙ n + x
```

```
≰0⇒≥1 : {x : O} → ¬ x ≤ zer → uno ≤ x
-- Holify
≰0⇒≥1 {zer}        p with p ≤-zer
... | ()
≰0⇒≥1 {suc x}      p = ≤-suc-mon ≤-zer
≰0⇒≥1 {lim f fmon} p = ≤-trans (≤-suc-mon ≤-zer) (≤-cocone (fmon zero))
```

```
·ₙ-mon : (x : O) → ¬ x ≤ zer → (n : ℕ) → x ·ₙ n < x ·ₙ succ n
·ₙ-mon x p n = +-mon {x ·ₙ n} {uno} {x} (≰0⇒≥1 p)
```

```
_·ω : O → O
x ·ω with zer? x
... | left  x≈zer = zer
... | right x≉zer = lim (λ n → x ·ₙ n) (·ₙ-mon x λ p → x≉zer (p , ≤-zer))
```


## Exponentiation by ω

::: Todo :::
Write.
:::


<!--
## Ordinal multiplication

```code
infixl 7 _·_
_·_ : O → O → O
·-mon : {x a b : O} → a ≤ b → (x · a) ≤ (x · b)
```

```code
a · zer        = zer
a · suc b      = (a · b) + a
a · lim f fmon with zer? a
... | left  _ = zer
... | right _ = lim (λ n → a · f n) (λ n → {!!})
```

Now you are asked to fill in the required lemma.

```code
·-mon p = {!!}
```
-->


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
