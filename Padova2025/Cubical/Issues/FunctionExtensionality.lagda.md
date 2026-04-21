```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Cubical.Issues.FunctionExtensionality where
```

# Function extensionality

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```

Let us consider the following three function definitions.

```
example₁ : Bool → Bool
example₁ x = x

example₂ : Bool → Bool
example₂ false = false
example₂ true  = true

example₃ : Bool → Bool
example₃ false = false
example₃ true  = true
-- Yes, identical to the definition of example₂.
```

Obviously, these functions have the same values on all inputs:

```
all-same₁₂ : (x : Bool) → example₁ x ≡ example₂ x
all-same₁₂ false = refl
all-same₁₂ true  = refl

all-same₂₃ : (x : Bool) → example₂ x ≡ example₃ x
all-same₂₃ false = refl
all-same₂₃ true  = refl
```

**Not provably the same.**
However, in standard Agda we cannot prove that the functions themselves are
the same---the following holes cannot be filled (and the proposal `refl` does
not typecheck):

```code
_ : example₁ ≡ example₂
_ = ?

_ : example₂ ≡ example₃
_ = ?
```

**Not provably distinct.**
On the other hand, in Agda we can also not prove the three functions above to
be distinct, that is we cannot write down terms of type `exampleᵢ ≡ exampleⱼ → ⊥`.
[Agda is (like any other reasonable formal system)
incomplete.](https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems)
This particular instance of incompleteness is particularly worrying to some, as it pertains to
such a basic part of Agda. *The equality type is underspecified.*

**A principle.**
The principle that functions with equal values are themselves equal is known as
*function extensionality*. Blackboard mathematics has it, while standard Agda
does not.

```
FunctionExtensionality : Set₁
FunctionExtensionality = {X Y : Set} {f g : X → Y} → ((x : X) → f x ≡ g x) → f ≡ g
```


## Postulating function extensionality

We may, if we prefer, postulate function extensionality:

```code
postulate
  funext : FunctionExtensionality
```

Adding function extensionality to Martin-Löf type theory preserves its
consistency. Moreover, if one entertains the idea of a platonic heaven of the usual sort, then
one can rest assured that the resulting type theory still provides an apt
language for talking about the objects of the platonic heaven.

However, by postulating function extensionality we lose *canonicity*:
With this postulate, it can happen that elements of inductively defined types
do not reduce to a constructor call. A basic example is already provided by
`funext` itself.

```code
does-not-reduce-to-refl : example₁ ≡ example₂
does-not-reduce-to-refl = funext all-same₁₂
```

```code
does-not-reduce-to-a-numeral : ℕ
does-not-reduce-to-a-numeral = check does-not-reduce-to-refl
  where
  check : {g : Bool → Bool} → example₁ ≡ g → ℕ
  check refl = zero
```


## Avoiding function extensionality

For many purposes, function extensionality can easily be avoided by
employing [pointwise equality](Padova2025.ProvingBasics.Equality.General.html#_≗_) instead of true `_≡_`, as follows.

```
all-same₁₂' : example₁ ≗ example₂
all-same₁₂' = all-same₁₂
```

But it is also desirable to actually have function
extensionality. Such a system is offered by Cubical Agda.


## Exercise: Pointwise equality is an equivalence relation

```
≗-refl : {X Y : Set} {f : X → Y} → f ≗ f
-- Holify
≗-refl x = refl
```

```
≗-sym : {X Y : Set} {f g : X → Y} → f ≗ g → g ≗ f
-- Holify
≗-sym p x = sym (p x)
```

```
≗-trans : {X Y : Set} {f g h : X → Y} → f ≗ g → g ≗ h → f ≗ h
-- Holify
≗-trans p q x = trans (p x) (q x)
```


## Exercise: Types form a category

Let `f`, `g` and `h` be composable functions. Then we definitely have
`(h ∘ g) ∘ f ≗ h ∘ (g ∘ f)`. Does the same identity also hold with
`_≡_` in place of `_≗_`, or is function extensionality needed for that?

::: More :::
```
open import Padova2025.ProgrammingBasics.HigherOrder
open import Padova2025.ProgrammingBasics.DependentFunctions
```

Even though standard Agda does not have function extensionality, it
does have *eta equality*: Every function `f` is judgmentally equal to
the lambda `λ x → f x`. This principle is enough to verify that the
(small) types form a category, up to true propositional equality
and not only up to pointwise equality.

```
∘-assoc : {X Y Z W : Set} → (f : X → Y) (g : Y → Z) (h : Z → W) → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
-- Holify
∘-assoc f g h = refl
```

```
∘-identityˡ : {X Y : Set} → (f : X → Y) → id Y ∘ f ≡ f
-- Holify
∘-identityˡ f = refl
```

```
∘-identityʳ : {X Y : Set} → (f : X → Y) → f ∘ id X ≡ f
-- Holify
∘-identityʳ f = refl
```

Having established that types form a category, a category
theorist might enquire about its categorical properties. For instance, in
blackboard mathematics, the category $\mathrm{Set}$ has an initial
object, namely the empty set $∅$: For every set $X$, there is exactly
one map $∅ → X$.

Does the category of types have an initial object? How about a
terminal object?

::: More :::

### No initial object

Agda does have the empty type `⊥`, and for every type `X` there is a
map [`⊥-elim : ⊥ → X`](Padova2025.ProvingBasics.Negation.html#⊥-elim).
Hence the category of types has a *weakly initial object*.
However, without function extensionality, we cannot show that any two
functions of type `⊥ → X` are identical.


### Terminal object

On the other hand, there is a terminal object. This is provided by the
following declaration.

```
record 𝟙 : Set where
  constructor tt
```

Record types by default have
[(their own version of) eta equality](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion).
That is the reason why any two inhabitants are judgmentally equal:

```
_ : (x y : 𝟙) → x ≡ y
_ = λ x y → refl
```

As a corollary, any two functions to `𝟙` are judgmentally equal:

```
_ : {X : Set} → {f g : X → 𝟙} → f ≡ g
_ = refl
```

In contrast, declaring `𝟙` as an ordinary inductive datatype (or disabling eta equality with the
`no-eta-equality` keyword in the record declaraction) will provide us
with a type in which any two inhabitants are propositionally but not judgmentally equal.
This type is not terminal in the category of small types.

```
data 𝟙' : Set where
  tt : 𝟙'

𝟙'-isProp : (x y : 𝟙') → x ≡ y
𝟙'-isProp tt tt = refl
-- But without the pattern match, 𝟙'-isProp x y = refl, there is a type error.
```


### Category of setoids

Even though the category of types is perhaps the first to reach out to
when exploring the landscape of categories in Agda, the category of (small)
*setoids* is for many applications actually much more sensible, less dependent
on foundations (such as the availability or non-availability of function
extensionality) and also much better behaved. For instance, the category of
setoids is complete and cocomplete, locally cartesian closed, exact and extensive.
It also validates a version of the axiom of choice. All of these assertions can be
explored in great detail in the
[categories library](https://github.com/agda/agda-categories) in the
[module Categories.Category.Instance.Properties.Setoids and its
submodules](https://agda.github.io/agda-categories/index.html).
:::
:::
