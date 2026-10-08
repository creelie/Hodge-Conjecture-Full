# What is still open

This is the Hodge part of a survey of the author's reference repositories,
made while looking for a gap small enough to close by a purely analytical
argument. None closes.

## Weil classes on abelian varieties

What is left for abelian varieties is the Weil class on a *general* member
of a Weil-type family. The closure theorem of H8 (`H8/tex/sections/14_closure.tex`,
item (ii)) reduces this, for each triple (K, n, δ), to the algebraicity of
one explicit class at every point of an n²-dimensional period domain, and
shows that the algebraic locus is either everything or meagre. The same
section lists more than a dozen constructions that provably cannot produce
the class.

Cycles at members with full Hodge group do exist in one case: Schoen's
cycles on Prym varieties of étale triple covers, for Q(√−3) and a split
form. They are the three lifts of the canonical system |K| ≅ Pⁿ of the base
curve to the triple cover of its symmetric power. The Prym locus has
dimension 3n inside a family of dimension n², so it fills the family only
for n ≤ 3. Theorem 5.2 of `paper/full_attempt.tex` pushes the cycles to the
Prym variety and finds there one irreducible n-dimensional subvariety Y
whose class, at a very general Prym, is a positive multiple of ηⁿ plus a
nonzero Weil class. For n ≥ 4 the question is whether Y is semiregular. The
Abel–Jacobi curve in a Jacobian, built from the same map, is not
semiregular once g ≥ 4 (Matsusaka–Ran and Bloch), which points against it.
This is undecided.

## The other two statements of H8's route

H8 lists three inputs still missing from its route to the full conjecture:
propagation for the split families of CM fields of degree at least four;
(F2), the Hodge classes on abelian varieties beyond divisor and Weil
classes; and (F3'), the conjecture modulo abelian varieties.

- (F2) contains the two exceptional classes on the square of a Mumford
  fourfold. H8 shows they are algebraic once a Kuga–Satake class of a K3
  surface of Picard number thirteen is, and that class is not known to be
  algebraic.
- (F3') holds on varieties whose cohomology is reached from abelian
  varieties, in low degree and dimension, and on Delsarte fourfolds. Beyond
  that it is open. It contains, for example, the Hodge classes on S × S for
  a K3 surface S with real multiplication, which are open in general.

None of the three is closed here.
