```
module Padova2025.Welcome.Rosetta where
```

# A mathematical Rosetta Stone

The following table is included here for ease of reference (and perhaps as a
kind of cryptic teaser). It will make more sense when we discuss how Agda can
be used as a proof language.

With the advent of _homotopy type theory_, a further column to this table was
discovered. We will discuss this expansion in the context of Cubical Agda.

| Blackboard mathematics | Agda |
| ---------------------- | ---- |
| A claim | A type (of witnesses) |
| Proving a claim | Exhibiting an element of the corresponding type |
| An unsound proof attempt | A term which does not type-check |
| Leaving a part of a proof attempt to be filled in later | Leaving a hole `?` |
| Realizing a missing assumption | Adding an extra argument |
| Assertion that $x = y$ | Type `x ≡ y` (a certain standard equality type) |
| Trivially equal by inspection | Witness `refl` |
| Arguing by induction | Defining a recursive function |
| Induction hypothesis | Recursive function call |
| Arguing by cases | Defining a function by pattern matching |
| Fixing an element $x \in A$ for the remainder of a section | Anonymous module `module _ (x : A) where` |
| Function application $f(x)$ | Function application `f x` |
| Result _foo_ applied to $x$ | Function application `foo x` |
| Result $P \Rightarrow Q$ | Function of type `P → Q` which transforms witnesses of type `P` into witnesses of type `Q` |
| Result $P \wedge Q$ | Element of `P × Q` (i.e. a pair of witnesses) |
| Result $P \vee Q$ | Element of `P ⊎ Q` (i.e. a witness of either) |
| Result $\forall(x \in A).\ P(x)$ | Function of type `(x : A) → P x` which reads an arbitrary `x` as input and produces a witness of `P x` as output |
| Result $\exists(x \in A).\ P(x)$ | Element of `Σ[ x ∈ A ] P x` (i.e. a pair `(x , p)` consisting of an element `x` and a witness of type `P x`) |
| Result $\neg P$ | Function of type `P → ⊥` |
| Contradiction/absurdity | Empty type `⊥` |
| A (small) subset of a set $A$ | A function `A → Set` |
| Class of all sets | Type `Set` of all small types (also spelled `Set₀`) |
| (Small) set | Small type, i.e. element of `Set` |
| Proper class | Type which is not an element of `Set` (but of `Setᵢ` for some nonzero universe level `i`) |
| A ring | A record bundling carrier, operations and laws |
| A commutative ring | A record with an extra commutativity field |
