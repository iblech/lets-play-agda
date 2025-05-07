```
module Padova2025.Explorations.CZF where
```

# Sets as trees

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Connectives
open import Padova2025.ProvingBasics.Termination.Gas
open import Agda.Primitive
```

Set theory and type theory in all their flavors can both be used as foundations
for large parts of mathematics. And they are interconnected: Within set theory,
we can build models of type theory, and within type theory, we can build models
of set theory. The latter is the purpose of this module: We will introduce a
type `V` whose elements represent sets as in set theory. We will have
constants like `∅` (representing the empty set) and `N` (representing the set of
natural numbers), functions like `union` (for taking the union of a set of
sets), a global membership relation called `_∈_`, and so on. We will then also
be able to study the properties of this model of set theory: Does the axiom of
choice hold? The powerset axiom?

The model we will describe is Peter Aczel's *sets as trees* model. We represent
sets by arbitrarily-branching trees; for instance, the set `{ x, {y,z},
{0,1,2,...} }` is represented by the following tree:

<pre style="line-height: 1.2em">
         *
        ╱│╲
       ╱ │ ╲
      ╱  │  ╲
     ╱   │   ╲
    ╱    │    ╲
   x     *     *
        ╱ ╲   ╱│╲
       y   z 0 1 2 ...
</pre>

In Agda, we express this idea as follows.

```
data V : Set₁ where
  sup : {I : Set} → (I → V) → V
```

The constructor `sup` takes an indexing type `I` and an `I`-indexed family of
trees and returns a new tree with those trees as the children of its root. In
the beginning, we do not know any trees; to get off the ground, we use the
empty family of trees:

```
∅ : V
∅ = sup {⊥} empty-function   -- just a root node without children
  where
  empty-function : ⊥ → V
  empty-function ()
```

Given trees `x` and `y`, we can create a new tree whose root has `x` and `y` as
its children:

```
pair : V → V → V
pair x y = sup {Bool} f  -- a root node with two children
  where
  f : Bool → V
  f false = x
  f true  = y
```

The following function is supposed to map a set `x` to the singleton set `{ x }`,
i.e. a tree `x` to a tree whose root has exactly one child, namely `x`.

```
singleton : V → V
-- Holify
singleton x = sup {𝟙} (λ _ → x)
```

The following function is supposed to input two sets `x` and `y`
and output the ordered _Kuratowski pair_ `{ {x}, {x,y} }`.

```
kuratowski : V → V → V
-- Holify
kuratowski x y = pair (singleton x) (pair x y)
```

For some results below, the following two projection functions are nice to have.
They allow us to access the indexing type or the family without having to
pattern match on the set in question.

```
Index : V → Set
Index (sup {I} f) = I
```

```
fam : (x : V) → Index x → V
fam (sup {I} f) = f
```


## The set-theoretic natural numbers

In set theory, the natural numbers are often bootstrapped from the empty set as
follows.

```code
0 ≔ {}
1 ≔ { 0 }       = { {} }                  = 0 ∪ {0}
2 ≔ { 0, 1 }    = { {}, {{}} }            = 1 ∪ {1}
3 ≔ { 0, 1, 2 } = { {}, {{}}, {{},{{}}} } = 2 ∪ {2}
```

In other words, a number is identified with its set of predecessors; the number
zero does not have any predecessors and is hence represented by the empty set.
To mimic this construction in Agda, let us implement the function `next` which
inputs a set `X` and outputs `X ∪ {X}`.

```
next : V → V
-- Holify
next x@(sup {I} f) = sup {Maybe I} g
  where
  g : Maybe I → V
  g nothing  = x
  g (just i) = f i
```

With `next` in place, we can convert every actual natural number into its
set-theoretic representation...

```
fromℕ : ℕ → V
-- Holify
fromℕ zero     = ∅
fromℕ (succ x) = next (fromℕ x)
```

...and thereby obtain the set of natural numbers:

```
N : V
N = sup {ℕ} fromℕ
```


## An equivalence relation

In set theory, the sets `{ x, y }` and `{ y, x }` are deemed equal; however,
in Agda, the trees `pair x y` and `pair y x` are distinct:

      *           *
     ╱ ╲   vs.   ╱ ╲
    x   y       y   x

We hence need to introduce an equivalence relation `_≈_` expressing that
two trees represent the same set.

```
infix 4 _≈_
_≈_ : V → V → Set
sup {I} f ≈ sup {J} g =
  ((i : I) → ∃[ j ] (f i ≈ g j)) ×
  ((j : J) → ∃[ i ] (g j ≈ f i))
-- "Every child `f i` is equivalent to one of the children of `sup g`,
-- and vice versa."
```

```
≈-refl : {x : V} → x ≈ x
-- Holify
≈-refl {sup f} = (λ i → i , ≈-refl) , (λ j → j , ≈-refl)
```

```
≈-sym : {x y : V} → x ≈ y → y ≈ x
-- Holify
≈-sym {sup f} {sup g} (p , p') = p' , p
```

```
≈-trans : {x y z : V} → x ≈ y → y ≈ z → x ≈ z
-- Holify
≈-trans {sup {I} f} {sup {J} g} {sup {K} h} (p , p') (q , q')
  = (λ i → fst (q  (fst (p  i))) , ≈-trans (snd (p  i)) (snd (q  (fst (p  i)))))
  , (λ k → fst (p' (fst (q' k))) , ≈-trans (snd (q' k)) (snd (p' (fst (q' k)))))
```


## The membership relation

Fundamental to set theory is the membership relation $\in$. This
relation is also responsible for one of the most discernible
differences between set theory and type theory: In set theory, for any
two sets $X$ and $Y$, the expression "$X \in Y$" is always a
well-defined assertion---perhaps provable, perhaps refutable, but in
any case a syntactically correctly formed proposition.

In contrast, in most flavors of type theory, the typing judgment `X :
Y` is never a mathematically interesting question. Instead, the typing
judgment is decidable---indeed, verifying well-typedness is what
Agda's kernel is all about. Either `X` is mechanically known to be of
type `Y`, or it has some other type (or is just ill-typed).

```
_∈_ : V → V → Set
x ∈ y = ∃[ i ] (fam y i ≈ x)
-- "x is an element of sup f iff it is equivalent to one of the
-- children of sup f."
```

```
cong-∈ : {x y z : V} → x ≈ y → z ∈ x → z ∈ y
-- Holify
cong-∈ {sup f} {sup g} {sup h} p (i , eq) = fst (fst p i) , ≈-sym (≈-trans (≈-sym eq) (snd (fst p i)))
```

```
cong-∈' : {x y z : V} → x ≈ y → x ∈ z → y ∈ z
-- Holify
cong-∈' {sup f} {sup g} {sup h} p (q , q') = q , ≈-trans q' p
```

As a basic sanity check, every child `f i` is an element of `sup f`; the
following is a convenience function for some of the proofs below.

```
∈-basic : {x : V} → (i : Index x) → fam x i ∈ x
-- Holify
∈-basic {sup {I} f} i = i , ≈-refl
```


## Axiom of extensionality

```
infix 4 _↔_
_↔_ : {ℓ ℓ' : Level} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A ↔ B = (A → B) × (B → A)
```

A basic principle in set theory is that sets are determined by their elements:
Two sets are equal if and only if they have the same elements. Our
sets-as-trees model of set theory validates this principle (if we replace
strict equality by `_≈_`).

```
extensionality₁ : {x y : V} → ((z : V) → z ∈ x ↔ z ∈ y) → x ≈ y
-- Holify
extensionality₁ {sup f} {sup g} p
  = (λ i → fst (fst (p (f i)) (i , ≈-refl)) , ≈-sym (snd (fst (p (f i)) (i , ≈-refl))))
  , (λ j → fst (snd (p (g j)) (j , ≈-refl)) , ≈-sym (snd (snd (p (g j)) (j , ≈-refl))))
```

```
extensionality₂ : {x y : V} → x ≈ y → ((z : V) → z ∈ x ↔ z ∈ y)
-- Holify
extensionality₂ p z = cong-∈ p , cong-∈ (≈-sym p)
```


## Basic set construction axioms

```
existence-empty-set : ∃[ x ] ((y : V) → y ∈ x → ⊥)
-- Holify
existence-empty-set = ∅ , λ { (sup f) () }
```

```
pairing-axiom : (x y : V) → ∃[ z ] (x ∈ z × y ∈ z)
-- Holify
pairing-axiom x y = pair x y , ((false , ≈-refl) , (true , ≈-refl))
```

```
union : V → V
-- Holify
union (sup {I} f) = sup {Σ I (λ i → Index (f i))} λ (i , j) → fam (f i) j
```

```code
union-axiom : (x : V) → ∃[ y ] ((z : V) → z ∈ y ↔ ∃[ w ] (z ∈ w × w ∈ x))
union-axiom x = ?
-- TODO: Format as exercise
```

<!--
union-axiom x@(sup {I} f) = union x , λ { z@(sup g)
  → (λ { ((i , j) , eq) → f i , cong-∈' {z = f i} eq (∈-basic {f i} j) , i , ≈-refl })
  , λ { (w , q@(j , eq') , i , eq) → ((i , {!fst ?!})) , ≈-trans {!!} eq' } }
-->


## In the vincinity of Russell's paradox

```
no-set-contains-itself : (v : V) → v ∈ v → ⊥
-- Holify
no-set-contains-itself (sup f) p@(i , eq) = no-set-contains-itself (f i) (cong-∈ (≈-sym eq) (cong-∈' {z = sup f} (≈-sym eq) p))
```

It is tempting to introduce a set `u` of all sets, as follows:

```code
u : V
u = sup {V} (λ x → x)
```

However, this attempt is rejected by Agda with the comment "`Set₁ != Set`
when checking that the expression `V` has type `Set`". The children of
a node need to be indexed by a small type, a type in `Set`; but `V`
itself is not a small type, but rather a type in `Set₁`.

Agda supports the unsafe option `--type-in-type`, collapsing the
universe hierarchy. The definition of `u` is then well-typed, and a
contradiction can be derived as follows.

```code
u∈u : u ∈ u
u∈u = u , ≈-refl

contradiction : ⊥
contradiction = no-set-contains-itself u u∈u
```

::: Todo :::
Make this explorable in a submodule
:::
