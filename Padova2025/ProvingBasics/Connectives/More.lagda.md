```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.ProvingBasics.Connectives.More where
```

# All and Any

```
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Existential
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


## Tabulation

```
tabulate : {A : Set} {P : A → Set} (xs : List A) → ({x : A} → x ∈ xs → P x) → All P xs
-- Holify
tabulate []       f = []
tabulate (x ∷ xs) f = f (here refl) ∷ tabulate xs (λ in-xs → f (there in-xs))
```


## All distributes over append

```
All-++-left : {A : Set} {P : A → Set} {ys : List A} (xs : List A) → All P (xs ++ ys) → All P xs
-- Holify
All-++-left []       _        = []
All-++-left (_ ∷ xs) (p ∷ ps) = p ∷ All-++-left xs ps
```

```
All-++-right : {A : Set} {P : A → Set} {ys : List A} (xs : List A) → All P (xs ++ ys) → All P ys
-- Holify
All-++-right []       ps       = ps
All-++-right (_ ∷ xs) (_ ∷ ps) = All-++-right xs ps
```

```
infixr 5 _++ᴬ_
_++ᴬ_ : {A : Set} {P : A → Set} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
[]       ++ᴬ ps' = {--}ps'{--}
(p ∷ ps) ++ᴬ ps' = {--}p ∷ (ps ++ᴬ ps'){--}
```


## Any distributes over append

```
Any-++-left : {A : Set} {P : A → Set} {xs : List A} {ys : List A} → Any P xs → Any P (xs ++ ys)
-- Holify
Any-++-left (here  p) = here p
Any-++-left (there v) = there (Any-++-left v)
```

```
Any-++-right : {A : Set} {P : A → Set} {xs : List A} {ys : List A} → Any P ys → Any P (xs ++ ys)
-- Holify
Any-++-right {xs = []}     any = any
Any-++-right {xs = x ∷ xs} any = there (Any-++-right any)
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
-- Holify
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
and [`right`](Padova2025.ProvingBasics.Connectives.Disjunction.html#_⊎_.right).


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


## Almost everywhere equal functions

Two functions are deemed *almost everywhere equal* iff they differ only on
finitely many inputs

```
_≗*_ : {X Y : Set} → (X → Y) → (X → Y) → Set
f ≗* g = Σ[ xs ∈ List _ ] ((x : _) → f x ≡ g x ⊎ x ∈ xs)
```

Pointwise equal functions are equal almost everywhere:

```
≗→≗* : {X Y : Set} {f g : X → Y} → f ≗ g → f ≗* g
-- Holify
≗→≗* p = [] , λ x → left (p x)
```

The relation `_≗*_` is indeed an equivalence relation by the following lemmas.

```
≗*-refl : {X Y : Set} {f : X → Y} → f ≗* f
-- Holify
≗*-refl = [] , λ x → left refl
```

```
≗*-sym : {X Y : Set} {f g : X → Y} → f ≗* g → g ≗* f
-- Holify
≗*-sym (xs , p) = xs , λ x → ∨-map sym (λ z → z) (p x)
```

```
≗*-trans : {X Y : Set} {f g h : X → Y} → f ≗* g → g ≗* h → f ≗* h
-- Holify
≗*-trans {X} {Y} {f} {g} {h} (xs , p) (xs' , p') = xs ++ xs' , go
  where
  go : (x : X) → f x ≡ h x ⊎ x ∈ xs ++ xs'
  go x with p x | p' x
  ... | left eq    | left eq'    = left (trans eq eq')
  ... | left _     | right x∈xs' = right (Any-++-right x∈xs')
  ... | right x∈xs | _           = right (Any-++-left  x∈xs)
```

We will also use the occasion to define the notion of a *normalizer*
for functions `X → Y`. A normalizer picks for each `_≗*_`-equivalence class
a representative. Such normalizers exist by the axiom of choice
(which we will occasionally assume, to explore its consequences).

TODO explain records

```
record Normalizer (X Y : Set) : Set where
  field
    rep      : (X → Y) → (X → Y)
    rep≗*    : (f : X → Y) → rep f ≗* f
    respects : {f g : X → Y} → f ≗* g → rep f ≗ rep g
```

Unpacking: `rep` is the representative-picking function; `rep≗*`
says that what `rep` picks always lies in the same
equivalence class as its input; and `respects` is the
defining property of a choice function, stating that `rep` returns the
same representative for any two `_≗*_`-equivalent configurations.
