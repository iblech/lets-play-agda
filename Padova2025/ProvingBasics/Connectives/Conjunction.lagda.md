```
module Padova2025.ProvingBasics.Connectives.Conjunction where
```

# Conjunction

```
open import Agda.Primitive
open import Padova2025.ProvingBasics.Connectives.Existential
```

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

In particular, the functions [`fst`](Padova2025.ProvingBasics.Connectives.Existential.html#Σ) and
[`snd`](Padova2025.ProvingBasics.Connectives.Existential.html#Σ)
work also for these non-dependent products. Let us export these
functions for users importing this module.

```
open Padova2025.ProvingBasics.Connectives.Existential using (fst; snd) public
```


## Exercise: Tautologies involving conjunction

```
open import Padova2025.ProvingBasics.Negation
```

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


## Exercise: De Morgan's laws

```
open import Padova2025.ProvingBasics.Connectives.Disjunction
```

Verify the following three of the four De Morgan's laws.

```
de-morgan₁ : {A B : Set} → ¬ A × ¬ B → ¬ (A ⊎ B)
-- Holify
de-morgan₁ (f , g) (left  x) = f x
de-morgan₁ (f , g) (right y) = g y
```

```
de-morgan₂ : {A B : Set} → ¬ (A ⊎ B) → ¬ A × ¬ B
-- Holify
de-morgan₂ f = (λ x → f (left x)), (λ y → f (right y))
```

```
de-morgan₃ : {A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
-- Holify
de-morgan₃ (left  f) = λ (x , y) → f x
de-morgan₃ (right g) = λ (x , y) → g y
```

The fourth one, `¬ (A × B) → ¬ A ⊎ ¬ B`, would destroy the ability of
constructive mathematics to make finer distinctions between negative and
positive assertions. As Agda is by default a constructive system, the fourth
law is not provable in Agda.


## Exercise: Zero sum

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.NaturalNumbers
```

Prove that if a sum of natural numbers is zero, both summands are zero.

```
sum-zero : (a b : ℕ) → a + b ≡ zero → a ≡ zero × b ≡ zero
-- Holify
sum-zero zero     b p = refl , p
sum-zero (succ a) b ()
```
