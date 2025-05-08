```
module Padova2025.ProvingBasics.Connectives.More where
```

# All and Any

```
open import Padova2025.ProgrammingBasics.Lists
```

```
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
```

```
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
```

```
All-map : {A : Set} {P Q : A → Set} {xs : List A} → ({x : A} → P x → Q x) → All P xs → All Q xs
-- Holify
All-map f []       = []
All-map f (p ∷ ps) = f p ∷ All-map f ps
```


## Exercise: Zero sum, revisited

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Connectives.Conjunction
```

Prove that, if the sum over the elements of a list of natural numbers
is zero, then all elements are individually zero. The function
[`sum-zero`](Padova2025.ProvingBasics.Connectives.Conjunction.html#sum-zero)
might come in handy, but the direct solution is also attractive.

```
sum-zero' : (xs : List ℕ) → sum xs ≡ zero → All (_≡ zero) xs
-- Holify
sum-zero' []          p = []
sum-zero' (zero ∷ xs) p = refl ∷ sum-zero' xs p
-- Alternatively:
-- sum-zero' (x ∷ xs) p = fst (sum-zero x (sum xs) p) ∷ sum-zero' xs (snd (sum-zero x (sum xs) p))
```

The converse also holds:

```
sum-zero'' : (xs : List ℕ) → All (_≡ zero) xs → sum xs ≡ zero
-- Holify
sum-zero'' []          []         = refl
sum-zero'' (zero ∷ xs) (refl ∷ p) = sum-zero'' xs p
```


## Infinitude of the natural numbers

```
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Equality.General
```

One among several ways to express that there are infinitely many natural numbers is as follows:
For every finite list of natural numbers, there is a natural number not in that list. We can
formalize and prove this assertion as follows.

::: Todo :::
Prepare exercise
:::

<!--
```code
ℕ-infinite : (xs : List ℕ) → ∃[ x ] All (_≢ x) xs
ℕ-infinite xs = succ (sum xs) , lemma xs
  where
  lemma : (xs : List ℕ) → All (_≢ succ (sum xs)) xs
  lemma []       = []
  lemma (x ∷ xs) = {!!} ∷ All-map {!!} (lemma xs)
```
-->


## Decidable truth values

```
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProgrammingBasics.HigherOrder
```

In classical mathematics, where the law of excluded middle is
available, we have $A ∨ ¬A$ for any proposition $A$. In constructive
mathematics, where we strive to be more informative, we don't have
this principle available for arbitrary propositions, but we do have it
in many important special cases. If $A \vee \neg A$ holds, we say that $A$
is *decidable*.

In Agda, we define the type `Dec A` of witnesses that `A` is decidable as follows.

```
data Dec (A : Set) : Set where
  yes : A   → Dec A
  no  : ¬ A → Dec A
```

In other words, `Dec A` is just a variant of `A ⊎ ¬ A` with the
descriptive constructor names `yes` and `no` instead of
[`left`](Padova2025.ProvingBasics.Connectives.Disjunction.html#_⊎_.left)
and [`right](Padova2025.ProvingBasics.Connectives.Disjunction.html#_⊎_.right).


### Decidability of equality

```
infix 4 _≟_
_≟_ : (a b : ℕ) → Dec (a ≡ b)
a ≟ b = {--}∨-elim yes no (eq? a b){--}
```


### Decidability of implication

Prove that, if `A` and `B` are decidable, so is `A → B`.

```
dec-→ : {A B : Set} → Dec A → Dec B → Dec (A → B)
-- Holify
dec-→ (yes a)  (yes b)  = yes (λ f → b)
dec-→ (yes a)  (no  ¬b) = no  (λ f → ¬b (f a))
dec-→ (no  ¬a) q        = yes (λ a → ⊥-elim (¬a a))
```


### Finding elements with a specified property

```
find : {A : Set} {P : A → Set} → ((x : A) → Dec (P x)) → (xs : List A) → Any P xs ⊎ All (λ x → ¬ (P x)) xs
-- Holify
find P? [] = right []
find P? (x ∷ xs) with P? x | find P? xs
... | yes px  | _       = left  (here px)
... | no ¬px  | left  q = left  (there q)
... | no ¬px  | right q = right (¬px ∷ q)
```
