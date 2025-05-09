```
module Padova2025.ProvingBasics.Connectives.More where
```

# All and Any

```
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
```

The predicate `All P xs` expresses that `P` holds for all elements of the list
`xs`.

```
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
```

The predicate `Any P xs` expresses that `P` holds for at least one element of
the list.

```
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
```

As an application, `Any` can be used to define the membership predicate:

```
infix 4 _∈_ _∉_
_∈_ : {A : Set} → A → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → A → List A → Set
x ∉ xs = ¬ (x ∈ xs)
```


## Exercise: All and Any as functors

```
All-map : {A : Set} {P Q : A → Set} {xs : List A} → ({x : A} → P x → Q x) → All P xs → All Q xs
-- Holify
All-map f []       = []
All-map f (p ∷ ps) = f p ∷ All-map f ps
```

```
Any-map : {A : Set} {P Q : A → Set} {xs : List A} → ({x : A} → P x → Q x) → Any P xs → Any Q xs
-- Holify
Any-map f (here  p) = here (f p)
Any-map f (there v) = there (Any-map f v)
```


## Exercise: De Morgan's laws

Related to the exercise [on De Morgan's
laws](Padova2025.ProvingBasics.Connectives.Conjunction.html#exercise-de-morgans-laws)
in the binary case.

```
de-morgan₁ : {A : Set} {P : A → Set} {xs : List A} → All (λ x → ¬ P x) xs → ¬ Any P xs
-- Holify
de-morgan₁ (¬p ∷ ¬ps) (here  p) = ¬p p
de-morgan₁ (¬p ∷ ¬ps) (there q) = de-morgan₁ ¬ps q
```

```
de-morgan₂ : {A : Set} {P : A → Set} {xs : List A} → ¬ Any P xs → All (λ x → ¬ P x) xs
-- Holify
de-morgan₂ {xs = []}     ¬any = []
de-morgan₂ {xs = x ∷ xs} ¬any = (λ p → ¬any (here p)) ∷ de-morgan₂ (λ v → ¬any (there v))
```

```
de-morgan₃ : {A : Set} {P : A → Set} {xs : List A} → Any (λ x → ¬ P x) xs → ¬ All P xs
de-morgan₃ (here  ¬p) (p ∷ ps) = ¬p p
de-morgan₃ (there v)  (p ∷ ps) = de-morgan₃ v ps
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
