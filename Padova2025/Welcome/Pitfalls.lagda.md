# Common pitfalls

## Not being in a hole when case splitting

The keyboard shortcut `C-c C-c` for case splitting only works if the cursor is
currently inside a hole (`{!!}`). If the cursor is outside a hole, Agda will
report an error.

**Solution.** Move into the hole first.


## Forgetting variables on the left-hand side

When defining a function by pattern matching, every argument needs to
appear on the left-hand side of `=`. A common mistake is to forget
some arguments:

```code
-- wrong:
length = ...

-- right:
length xs = ...
```

If a variable is missing, Agda's types in the goal display will look
different from what you expect, with extra `→` arrows.

**Solution.** Add variable names for each argument on the left of the `=` sign.


## Forgetting to reload after adding a variable

You add a new variable to the left-hand side of a definition and then
immediately try to case split on it without first reloading the file. Agda does
not yet know about the new variable, so the case split will fail.

**Solution.** Always press `C-c C-l` (reload) after modifying code outside of
the current hole, before attempting further interactive commands like `C-c C-c`.


## Missing spacing around operators

Agda's lexer requires spaces around operators. The expression `a+b` is
interpreted as a single identifier named `a+b`, not as `a + b`.
Similarly, `a→b` is not `a → b`.

```text
-- wrong (single identifier "a+b"):
example = a+b

-- right:
example = a + b
```

**Solution.** Put spaces around operators.


## Missing parentheses in patterns

When pattern matching on a constructor which takes arguments (such as
`_∷_`), the pattern needs parentheses. Without parentheses, Agda will
interpret each part as a separate top-level pattern.

```text
-- wrong (three separate patterns instead of one):
head x ∷ xs = x

-- right:
head (x ∷ xs) = x
```


## Using ASCII fallbacks instead of Unicode

Some ASCII character sequences look similar to the Unicode symbols
used by modules of Let's play Agda, but to Agda they are entirely different identifiers. A common
mistake is using `::` (two ASCII colons) instead of `∷` (the Unicode
cons operator).

Hovering over a Unicode symbol on this website will show you how to
input it using the Agda input method.

**Solution.** Watch out for lookalikes.


## Mysterious yellow highlighting

When Agda highlights parts of your code in yellow, either you fell pray to a
rendering bug or Agda could not resolve some implicit arguments ("unsolved
metavariables").

**Solution.** First try reloading using `C-c C-l`. If the yellow highlighting
persists, explicitly supply the supposed-to-be implicit arguments.


## "Cannot split on local variable"

This error occurs if you ask Agda to case split on a variable in a
lambda expression such as `λ x → {!!}`.

**Solution.** To carry out such a case split,
first add enclosing curly braces: `λ { x → {!!} }`. After reloading,
case splitting will work.

Arguably this is a bug in the `C-c C-c` functionality, the required
curly braces should be inserted automatically.

<!--
```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Welcome.Pitfalls where
```
-->
