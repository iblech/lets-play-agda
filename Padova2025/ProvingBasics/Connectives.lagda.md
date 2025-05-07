```
module Padova2025.ProvingBasics.Connectives where
```

# Logical connectives

In the previous couple sections, we have already stated and proved quite a few
results. But we are still lacking the means to express other, quite basic,
assertions, such as the following:

1. **Every natural number is even or odd.** \
   $\forall(n \in \mathbb{N}).\ (\mathrm{Even}(n) \vee \mathrm{Odd}(n))$

2. **Every prime number greater than three is one more or one less than a multiple of six.** \
   $\forall(p \in \mathbb{P}).\ (p > 3 \Rightarrow (6 \mid p-1 \vee 6 \mid p+1))$

3. **Beyond every natural number, there is a prime number.** \
   $\forall(n \in \mathbb{N}).\ \exists(p \in \mathbb{N}).\ (p > n \wedge p \in \mathbb{P})$

The purpose of this module is to fill this gap, and introduce disjunction (∨),
conjunction (∧) and existential quantification (∃). Following the [propositions
as types philosophy](Padova2025.ProvingBasics.PropositionsAsTypes.html), we
should for instance introduce a suitable type of witnesses that a given number `n`
is even or odd. The first result above would then be formalized by a function
which reads an arbitrary number `n` as input and outputs such a kind of
witness.


## Disjunction

For expressing disjunction (∨), for given types `A` and `B` we introduce their
disjoint union `A ⊎ B`:

```
infixr 1 _⊎_
data _⊎_ (A : Set) (B : Set) : Set where
  left  : A → A ⊎ B
  right : B → A ⊎ B
-- In Haskell, `A ⊎ B` is known as `Either A B`.
```

In other words, the elements of `A ⊎ B` are of the form `left x` for some `x : A`,
or `right y` for some `y : B`. The computational reading is that `left` is a
function which inputs an element of type `A` and outputs an element of type `A
⊎ B`, and similarly with `right`. The logical reading is that `A` implies `A or B`.
The type of witnesses that a number `n` is even or odd is then `Even n ⊎ Odd n`.


### Exercise: Tautologies involving disjunction

```
open import Padova2025.ProvingBasics.Negation
```

```
∨-comm : {A B : Set} → A ⊎ B → B ⊎ A
-- Holify
∨-comm (left  x) = right x
∨-comm (right y) = left  y
```

```
∨-assoc : {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
-- Holify
∨-assoc (left  (left  x)) = left  x
∨-assoc (left  (right y)) = right (left  y)
∨-assoc (right z)         = right (right z)
```

```
∨-elim : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
-- Holify
∨-elim f g (left  x) = f x
∨-elim f g (right y) = g y
```

```
∨-map : {A A' B B' : Set} → (A → A') → (B → B') → A ⊎ B → A' ⊎ B'
-- Holify
∨-map f g (left  x) = left  (f x)
∨-map f g (right y) = right (g y)
```

```
∨-codiag : {A : Set} → A ⊎ A → A
-- Holify
∨-codiag (left  x) = x
∨-codiag (right y) = y
```

```
∨-not₁ : {A : Set} → A ⊎ ⊥ → A
-- Holify
∨-not₁ (left  x)  = x
∨-not₁ (right ())
```

```
∨-not₂ : {A B : Set} → A ⊎ B → ¬ B → A
-- Holify
∨-not₂ (left  x) f = x
∨-not₂ (right y) f = ⊥-elim (f y)
-- Alternatively, the second clause can be written as follows.
-- ∨-not₂ (right y) f with f y
-- ... | ()
```


### Exercise: Even or odd

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.DependentFunctions
open import Padova2025.ProvingBasics.EvenOdd
```

```
even-or-odd : (x : ℕ) → Even x ⊎ Odd x
-- Holify
even-or-odd zero            = left base-even
even-or-odd (succ zero)     = right base-odd
even-or-odd (succ (succ x)) with even-or-odd x
... | left  p = left  (step-even p)
... | right p = right (step-odd p)
```

```
not-odd-implies-even : (x : ℕ) → ¬ Odd x → Even x
-- Holify
not-odd-implies-even x p = ∨-not₂ (even-or-odd x) p
```


## Existential quantification

A witness for an existential quantification "there exists a value `x : A` such
that `P x`" should be a pair consisting of a suitable value `x : A` and a
witnesses of type `P x`. Hence we introduce, for any type `A` and any
predicate `P : A → Set`, the following dependent pair type.

```code
infixr 4 _,_
data Σ (A : Set) (P : A → Set) : Set where
  _,_ : (fst : A) → (snd : P a) → Σ A P
```

::: Aside :::
While this definition is just fine, we will actually use the following one.

```
open import Agda.Primitive

infixr 4 _,_
record Σ {ℓ ℓ' : Level} (A : Set ℓ) (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    fst : A
    snd : P fst
open Σ public
```

The difference is twofold. Firstly, we use `record` instead of `data`. Record
types have the advantage that they support
[eta equality](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion):
Without having to pattern match on a value `w` of type `Σ A P`, such a value is
judgmentally equal to `(fst w , snd w)`.

Secondly, we allow the type `A` and the values of the `P` function to be larger
kinds of types, i.e. types in `Set₁` or higher, instead of restricting to the base
universe `Set`. This extra generality is useful for later developments. It
would be a nuisance to have to redefine the dependent pair construction then.
:::


### Syntactic sugar

```
∃-syntax : {ℓ ℓ' : Level} {A : Set ℓ} → (A → Set ℓ') → Set (ℓ ⊔ ℓ')
∃-syntax = Σ _

syntax ∃-syntax (λ x → P) = ∃[ x ] P
```


### Exercise: Tautologies involving existential quantification

```
infinitary-de-morgan₁ : {A : Set} {P : A → Set} → ((x : A) → ¬ P x) → ¬ ∃[ x ] P x
-- Holify
infinitary-de-morgan₁ f (x , p) = f x p
```

```
infinitary-de-morgan₂ : {A : Set} {P : A → Set} → ¬ ∃[ x ] P x → ((x : A) → ¬ P x)
-- Holify
infinitary-de-morgan₂ f x p = f (x , p)
```

```
∃-∨ : {A B : Set} {P : B → Set} → ∃[ x ] (P x ⊎ B) → (∃[ x ] P x) ⊎ B
-- Holify
∃-∨ (x , left  p) = left  (x , p)
∃-∨ (x , right b) = right b
```


### Remark: A variety of formalizations of evenness

[Back when introducing
predicates](Padova2025.ProvingBasics.EvenOdd.html), we have chosen one
particular definition of evenness. But other formalizations are also
possible. Let us collect here all the auxiliary results showing that
several of those notions coincide.

```
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

```
Even₁ Even₂ Even₃ Even₄ : ℕ → Set

Even₁ n = Even n
Even₂ n = ¬ Odd n
Even₃ n = Odd (succ n)
Even₄ n = ∃[ m ] (n ≡ twice m)
```

```
1⇒2 : {n : ℕ} → Even₁ n → Even₂ n
2⇒1 : {n : ℕ} → Even₂ n → Even₁ n
1⇒3 : {n : ℕ} → Even₁ n → Even₃ n
3⇒1 : {n : ℕ} → Even₃ n → Even₁ n
1⇒4 : {n : ℕ} → Even₁ n → Even₄ n
4⇒1 : {n : ℕ} → Even₄ n → Even₁ n

1⇒2 = even-and-odd
2⇒1 = not-odd-implies-even _
1⇒3 = succ-even
3⇒1 = succ-even'
1⇒4 p = half _ , even-twice p
4⇒1 (m , p) = subst Even (sym p) (twice-even m)
```


## Conjunction

A witness for a conjunction `A and B` should consist of a witness of type `A`
and a witness of type `B`, i.e. a witness of a conjunction is a pair of
witnesses. This is just a special case of the dependent pair construction from
above. Hence we introduce, for any types `A` and `B`, the cartesian product
type `A × B`:

```
infixr 2 _×_
_×_ : {ℓ ℓ' : Level} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)
```


### Exercise: Tautologies involving conjunction

```
∧-comm : {A B : Set} → A × B → B × A
-- Holify
∧-comm (x , y) = (y , x)
```

```
∧-assoc : {A B C : Set} → (A × B) × C → A × (B × C)
-- Holify
∧-assoc ((x , y) , z) = (x , (y , z))
```

```
curry : {A B C : Set} → (A × B → C) → (A → (B → C))
-- Holify
curry f x y = f (x , y)
-- Alternatively: curry f = λx → λy → f (x , y)
```

```
uncurry : {A B C : Set} → (A → (B → C)) → (A × B → C)
uncurry f (x , y) = f x y
```

```
∧-map : {A A' B B' : Set} → (A → A') → (B → B') → A × B → A' × B'
-- Holify
∧-map f g (x , y) = (f x , g y)
```

```
∧-diag : {A : Set} → A → A × A
-- Holify
∧-diag x = (x , x)
```

```
∧-not : {A : Set} → A × ⊥ → ⊥
-- Holify
∧-not = snd
```

```
frobenius : {A B : Set} {P : A → Set} → ∃[ x ] (P x × B) → (∃[ x ] P x) × B
-- Holify
frobenius (x , (p , b)) = (x , p) , b
```


## All and Any

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


<!--
de Morgan
-->
