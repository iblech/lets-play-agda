```
{-# OPTIONS --cubical-compatible #-}
module Padova2025.Explorations.Forcing.Intro where
```

# Intro

In algebra and analysis, we are accustomed to extend given mathematical
structures to larger ones which are more suitable for certain tasks. For
instance, the sequence

> 3, 3.1, 3.14, 3.141, …

and many other fail to converge in ℚ, hence we enlarge ℚ to ℝ. Or the
field ℝ fails to contain a square root of $-1$, hence we enlarge ℝ to ℂ.

In the 1970s, Paul Cohen pioneered a technique for enlarging not a particular
mathematical structure such as a field or a ring, but to enlarge the given
the *mathematical universe itself*. For instance, starting from the base
universe, we can construct so-called
[forcing extensions](https://en.wikipedia.org/wiki/Forcing_(mathematics))
in which...

- there is a set of intermediate size between ℕ and ℝ ("Cohen forcing"),
- a given uncountable set $X$ of the base universe now appears countable ("Lévy collapse") or
- a "random real" exists ("random forcing").

Forcing became an invaluable tool for exploring the range of
set-theoretic possibility---which is quite large, as the axioms of
Zermelo--Fraenkel set theory vastly underspecify the notion of a set
(even if the axiom of choice is included).


## Applications in constructive mathematics

The utility of forcing was also recognized in the constructive
mathematics community, often in the guise of Grothendieck toposes,
where it helps us to extract computational content from classical
proofs.

For instance, given a commutative ring $R$ with unit, we can [enlarge
the universe to find a maximal ideal](https://github.com/iblech/constructive-maximal-ideals)
and thereby avoid using Zorn's lemma (which would concoct a maximal
ideal already in the base universe, but which is not available in
constructive mathematics).

Or we can enlarge the universe to contain a so-called *generic
$R$-algebra*, which is the starting point of synthetic algebraic
geometry. This account of algebraic geometry allows us to
do modern Grothendieck-style algebraic geometry (over arbitrary
base schemes) using a simple language reminiscient of the classical
Italian school of algebraic geometers (who worked only over ℂ),
avoiding the need to manage technicalities of schemes.


## Approximating from below

The key idea of forcing is to approximate the desired new set by
appropriate (often finite) sets of the base universe, just as we
approximate π by the rational numbers displayed above.

For instance, we can approximate a (phantastical) prime ideal in a
given commutative ring $R$ by finitely generated ideals
$\mathfrak{a}$. When we encounter the situation $xy ∈ \mathfrak{a}$,
we need to improve the approximation $\mathfrak{a}$ to $\mathfrak{a} +
(x)$ or $\mathfrak{a} + (y)$, to ensure the prime ideal condition
$xy ∈ \mathfrak{p} ⇒ (x ∈ \mathfrak{p} \vee y ∈ \mathfrak{p})$
in the limit.

Amazingly, this idea works even in cases where classical mathematics
proves that no limit exists. For instance, let $X$ be
an inhabited uncountable set such as $ℝ$. Then, by definition,
there is no surjection $ℕ ↠ X$. But we can approximate a fictional
such surjection by finite lists of elements of $X$: For instance,
we can regard the finite list `a ∷ b ∷ c ∷ []` as the partially-defined
barely-surjective function $f$ with $f(0) = a$, $f(1) = b$ and $f(2) = c$.
Over time, this approximation could evolve to a list of the form `a ∷ b ∷ c ∷ x ∷ []`,
where `x` ranges over the elements of $X$, in order to make $f$ more defined;
or it could evolve to a list of the form `a ∷ b ∷ c ∷ xs`, where `xs` ranges
over the finite lists of elements of $X$ in such a way that the new
approximation includes a given element `w` as one of its terms, in order
to make $f$ more surjective.

Giving a precise account of forcing in Agda, which is true in all
details to usual presentations of Grothendieck toposes in blackboard
mathematics, is a challenge. In the next sections, we will explore a
simplified version which has certain issues, but still allows us to
play with this circle of ideas (and manage to state and prove
instructive results).
