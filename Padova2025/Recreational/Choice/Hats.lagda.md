```
{-# OPTIONS --cubical-compatible #-}

open import Padova2025.ProgrammingBasics.Lists
open import Padova2025.ProgrammingBasics.HigherOrder
open import Padova2025.ProvingBasics.Equality.Base
open import Padova2025.ProvingBasics.Equality.General
open import Padova2025.ProvingBasics.Connectives.Existential
open import Padova2025.ProvingBasics.Connectives.Disjunction
open import Padova2025.ProvingBasics.Connectives.Conjunction
open import Padova2025.ProvingBasics.Connectives.More

module Padova2025.Recreational.Choice.Hats
  (Player : Set)
  (Color  : Set)
  (dummy  : Color)
  (_≡?_   : (p q : Player) → p ≡ q ⊎ p ≢ q)
  where
```

# The infinite hats problem

An evil monster puts hats of various colors on infinitely many
dwarves. Each dwarf can see (and cognitively process) the hat colors
of every other dwarf, but is strictly forbidden from peeking at their own
color. Instead, the monster will ask every one of them to privately
venture a guess regarding the color of their hat.

Is there a strategy which, if followed by the dwarves, ensures that
*only finitely many* of them guess their color incorrectly? The
strategy should be applicable regardless of the specific colors
assigned by the monster.

Communication among the dwarves is allowed only before the hats have
been placed. The type of colors is known (`Color`, fixed at the top of
this module), and so is the type of dwarves (`Player`), but nothing is
known about the distribution of colors chosen by the monster. Also
note that infinitely many dwarves being right does not necessarily
mean that only finitely many guess incorrectly. We assume that the
type of colors is inhabited (`dummy`).


## Obviously no successful strategy?

The challenge posed by the monster seems impossible to satisfy: The
monster is free to distribute the colors however it pleases; observing
the hat colors of all the other dwarves does not restrict the number
of possibilities for your own hat color in any way.

Surprisingly, despite appearances, there does exist a successful
strategy---if and only if (a certain instance of) the axiom of choice
holds. We will explore this below. (Whether the dwarves have access to
this strategy is a different question.)


## Formalizing the problem

A *configuration* is a possible distribution of hat colors to players:

```
Config : Set
Config = Player → Color
```

A *blinded configuration* (for a specific player `p`) is a function
which maps every player, with the exception of `p`, to a color:

```
BlindedConfig : Player → Set
BlindedConfig p = (q : Player) → q ≢ p → Color
```

Given a configuration, we can restrict its domain to obtain a blinded configuration.

```
blind : (p : Player) → Config → BlindedConfig p
blind p c = λ q _ → c q
```

A *player strategy* (for a player `p`) tells `p` which color to submit as
their guess, given knowledge of the colors of all other players:

```
PlayerStrategy : Player → Set
PlayerStrategy p = BlindedConfig p → Color
```

A *team strategy* tells every player which player strategy to use:

```
TeamStrategy : Set
TeamStrategy = (p : Player) → PlayerStrategy p
```

Given a configuration and a team strategy, we can solicit every player for their guess,
thereby obtaining a configuration of guesses:

```
run : TeamStrategy → Config → Config
run s c p = s p (blind p c)
```

Finally, we can formalize the notion of a *successful team strategy*.
The relation `_≗*_` used in the following definition is defined in
[Padova2025.ProvingBasics.Connectives.More](Padova2025.ProvingBasics.Connectives.More.html#_≗*_)
and expresses that two configurations differ only on finitely many players.

```
isSuccessful : TeamStrategy → Set
isSuccessful s = (c : Config) → run s c ≗* c
```


## Some observations

Given a blinded configuration and a color, we obtain a full configuration:

```
unblind : (p : Player) → BlindedConfig p → Color → Config
unblind p c x q with q ≡? p
... | left  _   = x
... | right p≢q = c q p≢q
```

Unblinding a blinded configuration with an arbitrary color will result in an almost
identical configuration:

```
unblind-blind : (c : Config) (x : Color) (p : Player) → unblind p (blind p c) x ≗* c
-- Holify
unblind-blind c x p = p ∷ [] , go
  where
  go : (q : Player) → unblind p (blind p c) x q ≡ c q ⊎ q ∈ p ∷ []
  go q with q ≡? p
  ... | left  q≡p = right (here q≡p)
  ... | right q≢p = left  refl
```


## A successful strategy

Spoiler alert.

::: More :::
Let us partition the type of configurations into equivalence classes according to `_≗*_`.
By the axiom of choice, there is a choice function picking representatives for
each class. Reformulating this without explicitly referring to equivalence classes,
the axiom of choice concocts a value of the type
[`Normalizer Player Color`](Padova2025.ProvingBasics.Connectives.More.html#Normalizer).

::: More :::
With a shared such choice function at hand, we can assemble a
successful strategy for the players as follows. Even though each
player is in the dark about which configuration precisely the evil
monster has picked, each player can with certainty determine the
equivalence class of the true configuration. When asked for a guess
for their own color, each player should answer with whatever their
color is in the chosen representative of this class. Since the
representative is guaranteed to differ from the true configuration
only on finitely many players, only finitely many players guess
incorrectly.

Let us implement this idea in Agda.

```
assembleStrategy : (Config → Config) → TeamStrategy
-- Holify
assembleStrategy r p bc = r (unblind p bc dummy) p
```

```
correct : (r : Normalizer Player Color) → isSuccessful (assembleStrategy (Normalizer.rep r))
-- Holify
correct r c = ≗*-trans (≗→≗* run≗r) (rep≗* c)
  where
  open Normalizer r
  run≗r : run (assembleStrategy rep) c ≗ rep c
  run≗r p = respects (unblind-blind c dummy p) p
```

*And here we leave the dwarves at their campfire, in the long night
that awaits them: How many evenings---how many lifetimes---will pass
before they have agreed on a single representative for
each of the uncountably many equivalence classes?*

:::
:::
