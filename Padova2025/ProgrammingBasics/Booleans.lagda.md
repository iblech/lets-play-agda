```
module Padova2025.ProgrammingBasics.Booleans where
```

# Booleans

The type `Bool` contains precisely two values, `false` and `true`:

```
data Bool : Set where
  false : Bool
  true  : Bool
```


## Exercise: Negation

Implement the negation function. It should map `false` to `true` and vice
versa:

```agda/hole
not : Bool → Bool
not false = true
not true  = false
```


## Exercise: Identity function

```
id : Bool → Bool
id = {!!}
```
