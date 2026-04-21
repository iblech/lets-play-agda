# Welcome // Let's play Agda: running abstract mathematical proofs as programs

The purpose of this website is to help you learn Agda, the functional
proof language. It was created for a 2025 course at the [University of
Padova](https://www.unipd.it/en/dm).

**Start here:**
<span class="edit">[Agda as a programming language](Padova2025.ProgrammingBasics.Booleans.html)</span>

<!--<div style="background-color: mediumpurple; padding: 1em; color: white">-->
<div style="outline: 3px solid mediumpurple; padding: 0.5em; border: 1px solid transparent; border-radius: 0.3rem">
  👋 Padova students:
  <a href="https://agdapad.quasicoherent.io/~Padova2025/"><strong>Transcripts, recordings and links</strong></a>
  accompanying our sessions
</div>


## In a nutshell: Agda is a programming language...

- 🧊 **purely functional**, free of mutable state
- 🐑 **similar to Haskell** in syntax and vibe
- 🧱 **statically typed**, so that many errors are caught at compile-time
- 🌳 **familiar types** like integers, lists, …
- 🧭 **type inference**, so that we can focus on those types which matter

For instance, an implementation of insertion sort might look like this:

```code
sort : List ℕ → List ℕ
sort []       = []
sort (x ∷ xs) = insert x (sort xs)
```

And we can imagine functions with type signatures such as...

```code
fibonacci : ℕ → ℕ                                   -- Fibonacci numbers
pi        : ℝ                                       -- arbitrary-precision constant
size      : {X : Set} → Tree X → ℕ                  -- size of binary tree
replicate : {X : Set} (len : ℕ) → X → Vector len X  -- vector of identical elements
```


## ...and simultaneously: a proof language...

- 🧾 **types of witnesses** for unifying the activities of proving and
  programming
- ✨ **context assistance** for interactively constructing proofs
- 🎨 sufficiently **expressive** for vast parts of mathematics
- 🤹 **hole-driven development**

In Agda, we prove a proposition by constructing a program which computes a
suitable witness. This approach is the celebrated *propositions as types*
philosophy:

<pre><a href="Padova2025.ProvingBasics.Equality.FirstSteps.html#grande-teorema">grande-teorema</a>   : 2 + 2 ≡ 4
<a href="Padova2025.ProvingBasics.Equality.Reasoning.html#binomial-theorem">binomial-theorem</a> : (x : ℕ) (y : ℕ) → (x + y) ² ≡ x ² + 2 · x · y + y ²
<a href="Padova2025.VerifiedAlgorithms.InsertionSort.PostHoc.html#theorem">sort-correct</a>     : (xs : List ℕ) → IsSorted (sort xs)</pre>

For instance, there is a type of witnesses...

- that `2 + 2` equals `4` <span class="inessential">(this type is
  inhabited)</span>;
- that `2 + 2` equals `5` <span class="inessential">(this type is empty)</span>;
- that there are prime numbers larger than 42 <span class="inessential">(this
  type contains infinitely many values, for instance the pair `(43 , p)`, where
  `p` is a witness that `43` is a prime larger than `42`)</span>;
- that there are infinitely many prime numbers;
- that a given sorting function `sort` works correctly
  <span class="inessential">(this type contains functions which read an
  arbitrary list `xs` as input and output a witness that `sort xs` is
  ascendingly ordered)</span>;
- that the continuum hypothesis holds;
- and so on.


## ...helping us with...

- ✅ verifying correctness of proofs
- 🧮 implementing algorithms
- 💭 structuring mathematical thoughts
- ⚙️ appreciating mathematics from a computational angle
- 🚀 collaboratively engineering mathematical libraries


<!--
```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Welcome where

import Padova2025.Welcome.About
import Padova2025.Welcome.GettingAgda
import Padova2025.Welcome.References
import Padova2025.Welcome.Pitfalls
import Padova2025.Welcome.Rosetta
```
-->
