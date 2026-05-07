#!/usr/bin/env bash

set -euo pipefail

# expect <key> <expected-value>
expect() {
  echo "Running type signature extraction test: $1..."
  if [ "$(jq -r --arg k "$1" '.[$k] // empty' "out/type-signatures.json")" != "$2" ]; then
    exit 1
  fi
}

# Multiline type signature
expect 'Padova2025.Explorations.Ordinals.html#lim-mon' \
  'lim-mon : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g} → ((n : ℕ) → f n ≤ g n) → lim f fmon ≤ lim g gmon'

# Multiline with apostrophe in name
expect "Padova2025.Explorations.Ordinals.html#lim-mon'" \
  "lim-mon' : {f g : ℕ → O} {fmon : Monotonic f} {gmon : Monotonic g} → ((n : ℕ) → f n ≤ g n) → lim f fmon ≤ lim g gmon"

# Single-line function
expect 'Padova2025.ProgrammingBasics.Lists.html#sum' \
  'sum : List ℕ → ℕ'

# Data type with parameter (should have "data " prefix, no "where")
expect 'Padova2025.ProgrammingBasics.Lists.html#List' \
  'data List (A : Set) : Set'

# Simple data type
expect 'Padova2025.ProgrammingBasics.Naturals.Base.html#ℕ' \
  'data ℕ : Set'

# Data type should not include constructors
expect 'Padova2025.ProgrammingBasics.Booleans.html#Bool' \
  'data Bool : Set'

# Record type (should have "record " prefix)
expect 'Agda.Builtin.Sigma.html#Σ' \
  'record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b)'

# Constructor
expect 'Padova2025.ProgrammingBasics.Lists.html#List._∷_' \
  '_∷_ : A → List A → List A'

# Negation: comment should be stripped
expect 'Padova2025.ProvingBasics.Negation.html#¬_' \
  '¬_ : Set → Set'

# Data type: "where" should be stripped even when tags have extra attributes
expect 'Padova2025.VerifiedAlgorithms.PL.html#Op' \
  'data Op : Set'
