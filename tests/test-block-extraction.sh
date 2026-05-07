#!/usr/bin/env bash

set -euo pipefail

# expect <block> — input on stdin, expected output on FD 3.
expect() {
  echo "Running block extraction test: $1..."
  diff -u <(cat <&3) <(AGDA_BLOCKNAME="$1" perl backend/extract-block.pl) || exit 1
}

expect return <<'INPUT' 3<<'EXPECTED'
```
return : {A : Set} → A → ¬ ¬ A
-- Holify
return x = λ k → k x
```
INPUT
-- EXERCISE STARTS
return : {A : Set} → A → ¬ ¬ A
return = {!!}
-- EXERCISE ENDS
EXPECTED

# Regression: name on its own line (take-drop, cons-subst, cast, ++V-assoc,
# ...) used to produce id="take-drop\n" because the id-capturing group in
# extract-block.pl was [^ ]* instead of \S*.
expect take-drop <<'INPUT' 3<<'EXPECTED'
```
take-drop
  : {A : Set} (k : ℕ) → P
-- Holify
take-drop zero xs = refl
```
INPUT
-- EXERCISE STARTS
take-drop
  : {A : Set} (k : ℕ) → P
take-drop = {!!}
-- EXERCISE ENDS
EXPECTED

expect '_<_' <<'INPUT' 3<<'EXPECTED'
```
infixl 4 _<_
_<_ : ℕ → ℕ → Set
_<_ = {--}?{--}
```
INPUT
-- EXERCISE STARTS
infixl 4 _<_
_<_ : ℕ → ℕ → Set
_<_ = {!!}
-- EXERCISE ENDS
EXPECTED

expect target <<'INPUT' 3<<'EXPECTED'
```
module M where
```

```
target : Set
target = {--}?{--}
```
INPUT
module M where

-- EXERCISE STARTS
target : Set
target = {!!}
-- EXERCISE ENDS
EXPECTED

expect foo <<'INPUT' 3<<'EXPECTED'
```sh
echo this is shell, not agda
```

```
foo : Set
foo = {--}?{--}
```
INPUT
-- EXERCISE STARTS
foo : Set
foo = {!!}
-- EXERCISE ENDS
EXPECTED

expect double <<'INPUT' 3<<'EXPECTED'
```
double : ℕ → ℕ
-- Holify
double n = n + n

-- Tests
-- EX: double 3 ≡ 6
```
INPUT
-- EXERCISE STARTS
double : ℕ → ℕ
double = {!!}
-- EXERCISE ENDS

-- Tests
module _ where private
  open import Padova2025.ProvingBasics.Equality.Base
  lets-play-agda-test : double 3 ≡ 6
  lets-play-agda-test = refl

EXPECTED
