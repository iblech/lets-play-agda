```
module Padova2025.VerifiedAlgorithms.Binary where
```

# Binary representation of natural numbers

We have defined the natural numbers in an unary manner, freely generating ℕ by
`zero` and `succ`; this approach is logically pleasing, but computationally
inefficient. Let us introduce binary representations of natural numbers, define
the basic arithmetical operations on binary representations, and then prove
these operations correct with respect to the unary model.

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.DependentFunctions
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Negation
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
open import Padova2025.ProvingBasics.Equality.Reasoning.Core
```

A binary representation is just a list of zeros and ones (with trailing zeros) allowed:

```
BitString : Set
BitString = List Bool
```

For instance, we represent the number 12 (binary `1100`) as `false ∷ false ∷
true ∷ true ∷ []`, i.e. with the least significant bit in the front. Every bit
string represents some natural number:

```
decode : BitString → ℕ
-- Holify
decode []           = zero
decode (false ∷ xs) = twice (decode xs)
decode (true  ∷ xs) = succ (twice (decode xs))

-- Tests
-- EX: decode [] ≡ zero
-- EX: decode (false ∷ true  ∷ []) ≡ two
-- EX: decode (true  ∷ true  ∷ []) ≡ three
-- EX: decode (true  ∷ false ∷ []) ≡ one
```


## Exercise: Binary successor

Implement the successor operation on bit strings, then prove it correct with
respect to the model.

```
succ₀ : BitString → BitString
-- Holify
succ₀ []           = true ∷ []
succ₀ (false ∷ xs) = true  ∷ xs
succ₀ (true  ∷ xs) = false ∷ succ₀ xs

-- Tests
-- EX: succ₀ (false ∷ true ∷ []) ≡ true ∷ true ∷ []
-- EX: succ₀ (true  ∷ true ∷ []) ≡ false ∷ false ∷ true ∷ []
```

```
succ₀-correct : (xs : BitString) → decode (succ₀ xs) ≡ succ (decode xs)
-- Holify
succ₀-correct [] = refl
succ₀-correct (false ∷ xs) = refl
succ₀-correct (true ∷ xs) = begin
  decode (succ₀ (true ∷ xs))      ≡⟨⟩
  decode (false ∷ succ₀ xs)       ≡⟨⟩
  twice (decode (succ₀ xs))       ≡⟨ cong twice (succ₀-correct xs) ⟩
  twice (succ (decode xs))        ≡⟨⟩
  succ (succ (twice (decode xs))) ≡⟨⟩
  succ (decode (true ∷ xs))       ∎
```


## Exercise: Encoding natural numbers

Implement a function which encodes a given natural number as a bit
string, then prove your implementation correct.

```
encode : ℕ → BitString
-- Holify
encode zero     = []
encode (succ x) = succ₀ (encode x)
```

::: Hint :::
The function `succ₀` from above might come in handy.
:::

```
decode-encode : (x : ℕ) → decode (encode x) ≡ x
-- Holify
decode-encode zero     = refl
decode-encode (succ x) = trans (succ₀-correct (encode x)) (cong succ (decode-encode x))
```


## Exercise: Uniqueness of binary representations

Every natural number admits infinitely many binary representations, as
we can always add trailing zeros. Let us prove that such trailing
zeros are the only source of non-uniqueness of binary representations.

To this end, we first define a predicate `AllZero : BitString → Set`
expressing that a given bit string consists just of zeros. Think about
how this could be done, then have a look at the following reference
definition.

::: More :::
```
data AllZero : BitString → Set where
  triv : AllZero []
  cons : {xs : BitString} → AllZero xs → AllZero (false ∷ xs)
```
:::

With the predicate `AllZero` at hand, we can define what it means that
two bit strings are equivalent:

```
infix 4 _≈_
data _≈_ : BitString → BitString → Set where
  base : {xs ys : BitString} → AllZero xs → AllZero ys → xs ≈ ys
  -- "Equivalent because both strings just consist of zeros."

  cons : {xs ys : BitString} {b : Bool} → xs ≈ ys → b ∷ xs ≈ b ∷ ys
  -- "Equivalent because both strings start the same, and then
  -- continue in an equivalent manner."
```

As a warm-up, let us prove that equivalent bit strings represent the
same natural number.

```
decode-allZero : {xs : BitString} → AllZero xs → decode xs ≡ zero
-- Holify
decode-allZero triv     = refl
decode-allZero (cons p) = cong twice (decode-allZero p)
```

```
decode-≈ : {xs ys : BitString} → xs ≈ ys → decode xs ≡ decode ys
-- Holify
decode-≈ (base p q)           = trans (decode-allZero p) (sym (decode-allZero q))
decode-≈ (cons {b = false} p) = cong twice (decode-≈ p)
decode-≈ (cons {b = true}  p) = cong succ (cong twice (decode-≈ p))
```

Now let us prove that bit strings which represent the same number are equivalent.

```
unique-zero : {xs : BitString} → decode xs ≡ zero → AllZero xs
-- Holify
unique-zero {[]}         p = triv
unique-zero {false ∷ xs} p = cons (unique-zero (twice-zero p))
  where
  twice-zero : {x : ℕ} → twice x ≡ zero → x ≡ zero
  twice-zero p = twice-injective p
```

```
unique : {xs ys : BitString} → decode xs ≡ decode ys → xs ≈ ys
-- Holify
unique {[]}         {ys}         p = base triv (unique-zero (sym p))
unique {x     ∷ xs} {[]}         p = base (unique-zero p) triv
unique {false ∷ xs} {false ∷ ys} p = cons (unique (twice-injective p))
unique {false ∷ xs} {true  ∷ ys} p = ⊥-elim (impossible-twice p)
unique {true  ∷ xs} {false ∷ ys} p = ⊥-elim (impossible-twice (sym p))
unique {true  ∷ xs} {true  ∷ ys} p = cons (unique (twice-injective (succ-injective p)))
```


## Exercise: Binary addition

Implement the addition operation on bit strings, then prove it correct with respect to the unary model.

```
add₀ : BitString → BitString → BitString
-- Holify
add₀ []           ys           = ys
add₀ (x ∷ xs)     []           = x ∷ xs
add₀ (false ∷ xs) (y ∷ ys)     = y ∷ add₀ xs ys
add₀ (true  ∷ xs) (false ∷ ys) = true ∷ add₀ xs ys
add₀ (true  ∷ xs) (true  ∷ ys) = false ∷ succ₀ (add₀ xs ys)
```

```
add₀-correct : (xs ys : BitString) → decode (add₀ xs ys) ≡ decode xs + decode ys
-- Holify
add₀-correct [] ys = refl
add₀-correct (x ∷ xs) [] = sym (+-zero (decode (x ∷ xs)))
add₀-correct (false ∷ xs) (false ∷ ys) = begin
  decode (add₀ (false ∷ xs) (false ∷ ys))   ≡⟨⟩
  decode (false ∷ add₀ xs ys)               ≡⟨⟩
  twice (decode (add₀ xs ys))               ≡⟨ cong twice (add₀-correct xs ys) ⟩
  twice (decode xs + decode ys)             ≡⟨ twice-homo (decode xs) (decode ys) ⟩
  twice (decode xs) + twice (decode ys)     ≡⟨⟩
  decode (false ∷ xs) + decode (false ∷ ys) ∎
add₀-correct (false ∷ xs) (true ∷ ys) = begin
  decode (add₀ (false ∷ xs) (true ∷ ys))       ≡⟨⟩
  decode (true ∷ add₀ xs ys)                   ≡⟨⟩
  succ (twice (decode (add₀ xs ys)))           ≡⟨ cong succ (cong twice (add₀-correct xs ys)) ⟩
  succ (twice (decode xs + decode ys))         ≡⟨ cong succ (twice-homo (decode xs) (decode ys)) ⟩
  succ (twice (decode xs) + twice (decode ys)) ≡˘⟨ +-succ (twice (decode xs)) (twice (decode ys)) ⟩
  twice (decode xs) + succ (twice (decode ys)) ≡⟨⟩
  decode (false ∷ xs) + decode (true ∷ ys)     ∎
add₀-correct (true ∷ xs) (false ∷ ys) = begin
  decode (add₀ (true ∷ xs) (false ∷ ys))       ≡⟨⟩
  decode (true ∷ add₀ xs ys)                   ≡⟨⟩
  succ (twice (decode (add₀ xs ys)))           ≡⟨ cong succ (cong twice (add₀-correct xs ys)) ⟩
  succ (twice (decode xs + decode ys))         ≡⟨ cong succ (twice-homo (decode xs) (decode ys)) ⟩
  succ (twice (decode xs) + twice (decode ys)) ≡⟨⟩
  succ (twice (decode xs)) + twice (decode ys) ≡⟨⟩
  decode (true ∷ xs) + decode (false ∷ ys)     ∎
add₀-correct (true ∷ xs) (true ∷ ys) = begin
  decode (add₀ (true ∷ xs) (true ∷ ys))               ≡⟨⟩
  decode (false ∷ succ₀ (add₀ xs ys))                 ≡⟨⟩
  twice (decode (succ₀ (add₀ xs ys)))                 ≡⟨ cong twice (succ₀-correct (add₀ xs ys)) ⟩
  twice (succ (decode (add₀ xs ys)))                  ≡⟨ cong twice (cong succ (add₀-correct xs ys)) ⟩
  twice (succ (decode xs + decode ys))                ≡⟨⟩
  succ (succ (twice (decode xs + decode ys)))         ≡⟨ cong succ (cong succ (twice-homo (decode xs) (decode ys))) ⟩
  succ (succ (twice (decode xs) + twice (decode ys))) ≡˘⟨ cong succ (+-succ (twice (decode xs)) (twice (decode ys))) ⟩
  succ (twice (decode xs) + succ (twice (decode ys))) ≡⟨⟩
  succ (twice (decode xs)) + succ (twice (decode ys)) ≡⟨⟩
  decode (true ∷ xs) + decode (true ∷ ys)             ∎
```
