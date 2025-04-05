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

-- Tests
-- EX: not false ≡ true
-- EX: not true  ≡ false
```

::: Hint :::
1. First introduce a variable to the left of the `=` symbol, i.e. have the line
   begin with `not x`.
2. Reload the file using C-c C-l, so that the hole activates.
3. Then, ensuring that the cursor is inside the hole, press C-c C-c and answer
   that you would like to do the case split on the variable `x`.
4. Finally, for each case, fill in the definition. Press C-c C-SPACE when you
   are finished with a hole.
5. Ask Agda to reload the file again using C-c C-l.
:::

## Exercise: Identity function

```
id : Bool → Bool
id = {!!}

-- Tests
-- EX: id false ≡ false
-- EX: id true  ≡ true
```
