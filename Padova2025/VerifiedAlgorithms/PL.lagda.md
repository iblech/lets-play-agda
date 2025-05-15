```
module Padova2025.VerifiedAlgorithms.PL where
```

# Case study: Compiler and interpreter

```
open import Padova2025.ProgrammingBasics.Naturals.Base
open import Padova2025.ProgrammingBasics.Naturals.Arithmetic
open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.Reasoning.Core
```

In this module, we first define the syntax for a toy programming language and
implement a reference evaluator. We then code up an emulator for a virtual
stack machine and write a compiler from the toy language to programs for this
stack machine. Finally, we verify the correctness of the compiler, relative to
the reference evaluator.

This module is based on Section 4 of
[Programming and Proving in Agda](https://github.com/jespercockx/agda-lecture-notes/raw/master/agda.pdf)
by Jesper Cockx.

```
data Expr : Set where
  lit : ℕ → Expr             -- literals (constants)
  add : Expr → Expr → Expr   -- addition
```

```
example : Expr
example = add (lit zero) (add (lit (succ zero)) (lit zero))
-- should evaluate to succ zero
```

```
eval : Expr → ℕ
eval (lit x)   = x
eval (add a b) = eval a + eval b
```

```
_ : eval example ≡ succ zero
_ = refl
```

```
-- The type of operations for our stack machine
data Op : Set where
  PUSH : ℕ → Op
  SUM  : Op
```

```
Stack : Set
Stack = List ℕ

Code : Set
Code = List Op
-- For instance, PUSH 3 ∷ PUSH 5 ∷ SUM is a value of type Code.
-- The list PUSH 3 ∷ SUM is also a value of type Code; however, running it will fail.
```

```
-- A simulator for our virtual machine
run : Code → Stack → Stack
run []           s             = s
run (PUSH x ∷ c) s             = run c (x ∷ s)
run (SUM ∷ c)    (a ∷ (b ∷ s)) = run c ((a + b) ∷ s)
run _            _             = []
```

```
-- A compiler for our toy programming language
compile : Expr → Code → Code
compile (lit x)   c = PUSH x ∷ c
compile (add a b) c = compile b (compile a (SUM ∷ c))
```

```
theorem : (e : Expr) (c : Code) (s : Stack) → run (compile e c) s ≡ run c (eval e ∷ s)
-- Holify
theorem (lit x)   c s = refl
theorem (add a b) c s = begin
  run (compile (add a b) c) s             ≡⟨⟩
  run (compile b (compile a (SUM ∷ c))) s ≡⟨ theorem b (compile a (SUM ∷ c)) s ⟩
  run (compile a (SUM ∷ c)) (eval b ∷ s)  ≡⟨ theorem a (SUM ∷ c) (eval b ∷ s) ⟩
  run c ((eval a + eval b) ∷ s)           ≡⟨⟩
  run c (eval (add a b) ∷ s)              ∎
```

```
compile₀ : Expr → Code
compile₀ e = compile e []
```

```
theorem₀ : (e : Expr) → run (compile₀ e) [] ≡ eval e ∷ []
theorem₀ e = theorem e [] []
```
