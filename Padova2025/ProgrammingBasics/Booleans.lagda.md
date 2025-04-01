# Booleans

```
module Padova2025.ProgrammingBasics.Booleans where
```

The type `Bool` contains precisely two values, `false` and `true`:

```
data Bool : Set where
  false : Bool
  true  : Bool
```


## Exercise: Negation

Implement the negation function. It should map `false` to `true` and vice
versa:

```agda/hide
not : Bool → Bool
not false = true
not true  = false
```

```
foo : Bool
foo = {--}false{--}
```
