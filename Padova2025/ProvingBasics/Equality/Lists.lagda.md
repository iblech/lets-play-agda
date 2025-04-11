```
module Padova2025.ProvingBasics.Equality.Lists where
```

# Results on lists

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
```


## Exercise: Double reverse

For the following exercise, note that `reverse (x ∷ xs)` is defined as
`reverse xs ∷ʳ x`.

```
reverse-∷ʳ : {A : Set} (ys : List A) (x : A) → reverse (ys ∷ʳ x) ≡ (x ∷ reverse ys)
-- Holify
reverse-∷ʳ []       x = refl
reverse-∷ʳ (y ∷ ys) x = cong (λ zs → zs ∷ʳ y) (reverse-∷ʳ ys x)
```

```
reverse-reverse : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
-- Holify
reverse-reverse [] = refl
reverse-reverse (x ∷ xs) =
  trans (reverse-∷ʳ (reverse xs) x) (cong (x ∷_) (reverse-reverse xs))
```


## Exercise: Associativity of concatenation

```
++-assoc : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
-- Holify
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
```


## Exercise: Length as a homomorphism

```
length-homo : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
-- Holify
length-homo []       ys = refl
length-homo (x ∷ xs) ys = cong succ (length-homo xs ys)
```


## Exercise: Replication as a natural transformation

```
replicate-natural
  : {A B : Set} (f : A → B) (n : ℕ) (x : A)
  → map f (replicate n x) ≡ replicate n (f x)
-- Holify
replicate-natural f zero     x = refl
replicate-natural f (succ n) x = cong (f x ∷_) (replicate-natural f n x)
```
