```
module Padova2025.ComputationalContent.Intro where
```

# Intro

## Constructive and nonconstructive proofs

Are there irrational numbers $x$ and $y$ such that their power $x^y$ is
rational? To recall, and to fix definitions, a real number is called *rational*
if and only if it is of the form $a/b$ with integers $a$ and $b$. (This is the
case if and only if the number has a periodic decimal expansion, like $1/3 =
0.333\ldots$) A number is called *irrational* if and only if it is not rational
(like √2).

By the following proof, the answer is *yes*:

**Theorem.** There are irrational numbers $x$ and $y$ such that $x^y$ is
rational.

*Proof.* Either √2<sup>√2</sup> is rational or not. In the first case, we
can set $x = √2$ and $y = √2$. In the second case, we can set $x$ =
√2<sup>√2</sup> and $y$ = √2; indeed, then $x^y$ = √2<sup>$√2 \cdot
√2$</sup> = √2² = 2 is rational. ∎

The question on the existence of irrational numbers whose power is rational is
thereby settled. However, a lingering feeling of discontent with the displayed
proof may remain: As long as we do not know which of the two cases holds,
we cannot point our finger at any particular example for such a pair of numbers.

Are there more informative proofs? Let us try again:

**Theorem.** There are irrational numbers $x$ and $y$ such that $x^y$ is
rational.

*Proof.* Set $x$ = √2 and $y$ = log<sub>√2</sub>(3). Then $x$ is well-known to
be irrational; the irrationality of $y$ might be less well-known but is
actually easier to establish than the irrationality of √2; and $x^y$ = 3 is
rational. ∎

This second proof is *constructive*, explicitly providing a witness for the
existential claim. In contrast, the first proof, which establishes truth but
does not disclose any witnesses, is dubbed *nonconstructive*. Such proofs are
accepted in *classical mathematics*, the standard flavor of mathematics; in
the alternative flavor of *constructive mathematics*, they are not.


## Unique features of constructive mathematics

In constructive mathematics, we embrace almost all axioms and rules of
inference of classical mathematics, but we do not use the law of excluded
middle ($A \vee \neg A$), we do not use the law of double negation elimination
($\neg\neg A \Rightarrow A$) and we do not use the axiom of choice. But on the
other hand we also do not postulate their negations: Instead we remain
neutrally agnostic about those principles. Hence every constructive proof is
also a valid classical proof. (Amazingly, a specific kind of converse holds as
well, but not in a literal sense.)

Constructive mathematics has a couple of unique features:

* Constructive proofs are more informative. For instance, constructively we are
  not allowed to establish that an equation has a solution by merely verifying that it is
  impossible for the equation to not have a solution. Instead, a constructive
  proof of existence needs to provide a witness, i.e. a pair of a value and a
  witness that the value indeed solves the equation.

* Constructive mathematics allows us to make finer distinctions, for instance
  between a set being inhabited (meaning that it contains an element) and the
  set merely not being empty (meaning that the assumption that it is empty
  implies a contradiction), or more generally between a statement and its
  double negation. These finer distinctions in turn have algorithmic and
  geometric consequences.)

* Every constructive result has an algorithmic interpretation---every
  constructive proof can be run as a computer program. For instance: Every constructive proof
  of the existence of a solution to an equation can be run as an algorithm
  computing such a solution. As Agda is by default a constructive system, we
  have observed this connection between logic and computability numerous times.

* Every constructive result has a geometric interpretation applying to
  continuous families. For instance, a theorem of constructive analysis states
  that every strictly monotone function ℝ → ℝ with a negative and a positive
  value has a zero. By the geometric interpretation of constructive proofs, we
  may immediately deduce that in every continuous family of strictly monotone
  functions with negative and positive values, locally their zeros can be
  picked in a continuous fashion. (A more involved example is given by the
  theorem of constructive linear algebra stating that every finitely generated
  vector space does *not not* have a basis. By the geometric interpretation, we
  may immediately deduce that every sheaf of finite type on a reduced scheme is
  *on a dense open* locally finitely free, i.e. Grothendieck's generic freeness
  lemma in algebraic geometry.)

* Constructive mathematics is compatible with intriguing but anti-classical
  axioms such as "every function ℝ → ℝ is continuous" or "every function ℕ → ℕ
  is computable".


## The surprising success of Hilbert's failed program

Can every result of classical mathematics be constructivized? Taken literally,
this question has a clear-cut negative answer. Many results are known to admit
only classical proofs, as they imply nonconstructive principles:

- Over Zermelo--Fraenkel set theory, the statement that every vector space has
  a basis implies the axiom of choice.
- Over Zermelo--Fraenkel set theory, the statement that every commutative ring
  has a maximal ideal implies the axiom of choice.
- Over intuitionistic Zermelo--Fraenkel set theory, the statement that every
  inhabited set of natural numbers contains a minimal element implies the law
  of excluded middle.

But these observations are just the beginning of a grander story. Hilbert made
a distinction between *abstract results*---typically of an infrastructural
nature---and *concrete results*, which concern more tangible mathematical
objects such as natural numbers. While many abstract results cannot be proven
constructively, their concrete consequences often can.

- The result that every function ℕ → ℕ has a minimal value is not available in
  constructive mathematics, yet its consequence Dickson's lemma is.
- The infinitary pigeonhole principle (stating that every infinite binary
  sequence contains infinitely many `false` terms or infinitely many `true`
  terms) is not available in constructive mathematics, yet its consequence the
  finitary pigeonhole principle is.
- The result that every commutative ring has a maximal ideal is not available
  in constructive mathematics, yet consequences about matrices are: For
  instance we do constructively have that only over the zero ring a matrix with
  more rows than columns can be surjective.

Classical proofs can in many cases be mined for constructive and hence computational content;
*classical proofs can thus be regarded as blueprints for more informative
constructive proofs*. In many cases, there are even formal meta-theorems
backing this philosophy, guaranteeing the feasibility of this extraction
endeavor. In this refined sense, Hilbert's program has been widely successful,
and auxiliary objects which can only be obtained by transfinite means, such as
minima of infinite sequences or maximal ideals, can be viewed as *convenient
fictions*: They are not strictly speaking available in constructive mathematics,
but they might as well be, because their consequences are.

The following modules are devoted to studying a particularly versatile
constructivization technique based on the *double negation monad*. This method
can be used to eliminate applications of the law of excluded middle from
classical proofs. (For eliminating applications of the axiom of choice, other
techniques are used, often based on formal topology or topos theory.)
