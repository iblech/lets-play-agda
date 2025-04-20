```
module Padova2025.Cubical.Issues.FunctionExtensionality where
```

# Function extensionality

```
open import Padova2025.ProgrammingBasics.Booleans
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProvingBasics.Equality.Base
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
However, in standard Agda we can not prove that the functions themselves are
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
be distinct, that is we cannot write down terms of type `exampleᵢ ≡ exampleⱼ →
⊥`. Agda is (like any other reasonable formal system) incomplete and the
equality type is underspecified.

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
consistency. Moreover, if one entertains the idea of a platonic heaven, then
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
employing pointwise equality instead of true `_≡_`, as follows.

```
_≈_ : {X Y : Set} → (X → Y) → (X → Y) → Set
f ≈ g = (x : _) → f x ≡ g x

all-same₁₂' : example₁ ≈ example₂
all-same₁₂' = all-same₁₂
```

But it is also desireable to actually have function
extensionality. Such a system is offered by Cubical Agda.
