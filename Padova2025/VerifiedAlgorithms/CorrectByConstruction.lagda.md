```
module Padova2025.VerifiedAlgorithms.CorrectByConstruction where
```

# Correct by construction

An alternative to post-hoc verification of the correctness of
algorithms is the *correct-by-construction approach*. By leveraging the
expressivity of dependent types from the beginning, the implementation
is guaranteed to work correctly---no separate verification needed.

We have already seen examples of this approach:

- [`eq? : (a b : ℕ) → (a ≡ b) ⊎ ¬ (a ≡ b)`](Padova2025.ProvingBasics.Connectives.Disjunction.html#eq?) from the module on disjunction--contrast with the
  [post-hoc treatment by `eq?-correct₁` and `eq?-correct₂`](Padova2025.VerifiedAlgorithms.PostHocVerification.html#eq?-correct₁).
- [`even-or-odd : (x : ℕ) → Even x ⊎ Odd x`](Padova2025.ProvingBasics.Connectives.Disjunction.html#even-or-odd)--contrast
  with the functions [`even?-correct₁` and `even?-correct₂`](Padova2025.VerifiedAlgorithms.PostHocVerification.html#even?-correct₁).

The main practical advantage of the correct-by-construction approach
is that often, less code is needed. Its main disadvantage is that the
intertwining of computationally meaningful values (i.e. natural numbers
being passed around) and computationally irrelevant values (witnesses
of certain assertions) can render the code harder to read.

We will explore correct-by-construction in more detail in a
[case study on insertion sort](Padova2025.VerifiedAlgorithms.InsertionSort.CorrectByConstruction.html).
Additional examples can be found in a
[tutorial by Jesper Cockx](https://jespercockx.github.io/ohrid19-agda/).
