```
{-# OPTIONS --cubical #-}
module Padova2025.Cubical.FirstSteps where
```

# First steps

```
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base renaming (_≡_ to _≡ᵢ_)
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
open import Padova2025.ProvingBasics.Termination.Gas using (𝟙; tt)
```

::: Todo :::
Proper introduction. Split off menagerie of types.
:::


## Unordered pairs

```
data UnorderedPair (A : Set) : Set where
  pair : (x y : A) → UnorderedPair A
  swap : (x y : A) → pair x y ≡ pair y x
```


## Generalities on equality

```
refl' : {X : Set} {a : X} → a ≡ a
refl' {a = a} = λ i → a
```

```
symm' : {X : Set} {a b : X} → a ≡ b → b ≡ a
symm' p = λ i → p (~ i)
```

```
cong' : {X Y : Set} {a b : X} → (f : X → Y) → a ≡ b → f a ≡ f b
cong' f p = {--}λ i → f (p i){--}
```

```
funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
-- Holify
funext h = λ i → λ x → h x i
```

Verifying transitivity is more difficult. Let us just use the function from
the cubical standard library:

```
trans' : {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
trans' p q = p ∙ q
```

```
≡ᵢ→≡ : {X : Set} {a b : X} → a ≡ᵢ b → a ≡ b
-- Holify
≡ᵢ→≡ refl = refl'
```

```
≡→≡ᵢ : {X : Set} {a b : X} → a ≡ b → a ≡ᵢ b
≡→≡ᵢ = J (λ b q → _ ≡ᵢ b) _≡ᵢ_.refl
```


## Exercise: Sum of unordered pair

```
sum-pair : UnorderedPair ℕ → ℕ
-- Holify
sum-pair (pair x y)   = x + y
sum-pair (swap x y i) = ≡ᵢ→≡ (+-comm x y) i
```


## Integers

```
infixl 5 _⊝_
data ℤ : Set where
  _⊝_    : (a b : ℕ) → ℤ
  cancel : (a b : ℕ) → a ⊝ b ≡ succ a ⊝ succ b
```

Define the successor and predecessor functions.

```
succℤ : ℤ → ℤ
succℤ (a ⊝ b)        = succ a ⊝ b
succℤ (cancel a b i) = {--}cancel (succ a) b i{--}
```

```
predℤ : ℤ → ℤ
predℤ (a ⊝ b)        = a ⊝ succ b
predℤ (cancel a b i) = {--}cancel a (succ b) i{--}
```


## Exercise: One is not zero, revisited

Show that one is not zero.

```
lemma-nontrivial : one ≡ zero → ⊥
-- Holify
lemma-nontrivial p = transport (λ i → disambig (p i)) zero
  where
  disambig : ℕ → Set
  disambig zero     = ⊥
  disambig (succ _) = ℕ  -- or any other inhabited type
```

::: Hint :::
With the inductive definition of `_≡_` we used before, this required
an empty pattern. Now that `_≡_` is no longer inductively defined,
but an in-built notion, we cannot case split on equality witnesses.

Instead, proceed as follows:

1. Define a function `disambig : ℕ → Set` which maps zero to ⊥
   and everything else to some inhabited type.
2. Assuming that there is a path `zero ≡ succ zero`, combine
   [`transport`](Cubical.Foundations.Prelude.html#transport) from the standard
   library and `disambig`:

       transport : {A B : Set} → A ≡ B → A → B
:::


## Exercise: Robustness of the unordered pair abstraction

Show that the unordered pair abstraction is not leaky, in the
sense that there cannot be a function which would extract the first
component of an unordered pair.

```
lemma-not-leaky : (f : UnorderedPair ℕ → ℕ) → ((a b : ℕ) → f (pair a b) ≡ a) → ⊥
-- Holify
lemma-not-leaky f p = lemma-nontrivial (symm' (p one zero) ∙ cong' f (swap one zero) ∙ p zero one)
```


## Mere propositions

In homotopy type theory, a type is called a *proposition* if and only
if all its inhabitants are equal. Hence all there is to know about a
proposition is whether it is inhabited.

```
isProp' : Set → Set
isProp' X = (a b : X) → a ≡ b
```

Show that the types `⊥` and `𝟙` are propositions in this sense.

```
⊥-isProp : isProp' ⊥
-- Holify
⊥-isProp ()
```

```
𝟙-isProp : isProp' 𝟙
-- Holify
𝟙-isProp tt tt = refl'
```

Show that negations are propositions.

```
lemma-negations-are-props : (X : Set) → isProp' (X → ⊥)
lemma-negations-are-props X f g = funext λ x → ⊥-isProp (f x) (g x)
```


## Zero-dimensionality of the type of natural numbers

In homotopy type theory, a type is called *hset* (or just *set*) iff
its identity types are mere propositions, i.e. iff there is at most
one path between any two elements.

```
isHSet : Set → Set
isHSet X = (a b : X) → isProp' (a ≡ b)
```

To verify that `ℕ` is an hset, we require an explicit description of its identity types.
For the following definition of `Code`, it will turn out that the types `a ≡ b` and `Code a b`
are equivalent.

```
Code : ℕ → ℕ → Set
Code zero     zero     = 𝟙
Code zero     (succ y) = ⊥
Code (succ x) zero     = ⊥
Code (succ x) (succ y) = Code x y
```

```
fromCode : (a b : ℕ) → Code a b → a ≡ b
-- Holify
fromCode zero     zero     p = refl'
fromCode (succ a) (succ b) p = cong' succ (fromCode a b p)
```

```
Code-refl : (a : ℕ) → Code a a
-- Holify
Code-refl zero     = tt
Code-refl (succ a) = Code-refl a
```

```
Code-isProp : (a b : ℕ) → isProp' (Code a b)
-- Holify
Code-isProp zero     zero     = 𝟙-isProp
Code-isProp zero     (succ b) = ⊥-isProp
Code-isProp (succ a) zero     = ⊥-isProp
Code-isProp (succ a) (succ b) = Code-isProp a b
```

```
toCode : (a b : ℕ) → a ≡ b → Code a b
toCode a b = J {--}(λ c q → Code a c){--} {--}(Code-refl a){--}
```

::: Hint :::
If `_≡_` was the inductively-defined equality predicate from before,
we would do a case split on `p` to reduce to the case `toCode a a
refl`; this case could be solved by `Code-refl a`.

This kind of case split is not available for `_≡_`, however
we can emulate its effects by the standard library's `J` function.
:::

```
from-to₀ : (a : ℕ) → fromCode a a (toCode a a refl') ≡ refl'
from-to₀ zero       = refl'
from-to₀ (succ a) i = cong succ (from-to₀ a i)
```

```
from-to : (a b : ℕ) → (p : a ≡ b) → fromCode a b (toCode a b p) ≡ p
from-to a b p = J (λ y q → fromCode a y (toCode a y q) ≡ q) (from-to₀ a) p
```

```
ℕ-isHSet : isHSet ℕ
-- Holify
ℕ-isHSet a b p q =
  symm' (from-to a b p) ∙ cong' (fromCode a b) (Code-isProp a b (toCode a b p) (toCode a b q)) ∙ from-to a b q
```
