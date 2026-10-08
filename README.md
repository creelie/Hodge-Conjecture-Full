# Weil Classes and the Hodge Conjecture

Deep Bhattacharjee

This repository holds the author's work on the Hodge conjecture for abelian
varieties of Weil type: a book manuscript prepared for Springer and the
research note it grew from. Every argument is analytical, and no proof here
depends on a computer calculation.

## Status

**The Hodge conjecture is not proved here.** On a general abelian variety of
Weil type the conjecture comes down to whether one explicit class, the Weil
class, is algebraic. The note and the book prove the following about the set
Σ of members of a Weil family on which that class is algebraic:

- Σ is a countable union of closed algebraic subsets, it is dense, and it is
  either the whole family or a meagre set.
- A positive-dimensional stratum of Σ through a member with full Hodge group
  has full monodromy.
- A single semiregular cycle or complex whose class is a nonzero Weil class
  plus a multiple of the polarization power would give Σ = the whole family,
  while an object whose Chern character is a pure Weil class is never
  semiregular.
- Deciding the question is equivalent to a uniform bound on the degrees of
  representing cycles along a Zariski-dense set (a variant of results in the
  author's earlier preprint, credited there).
- At a member with full Hodge group, no cycle built from divisors and
  homomorphisms, and no tautological cycle of a curve with an automorphism of
  order three, represents the class.

What remains open, and is stated as open in the text (see also
`notes/hodge-residuals.md`):

- the Weil class on general Weil-type abelian varieties of dimension 8 and
  more, and in dimension 6 outside the known families;
- whether one of Schoen's cycles on Prym varieties is semiregular, which
  would settle every dimension for Q(√−3) with split form
  (`paper/full_attempt.tex` shows these cycles give one explicit subvariety
  whose class is a positive multiple of the polarization power plus a
  nonzero Weil class, so the question is about that one subvariety);
- Hodge classes on abelian varieties beyond divisor and Weil classes, and the
  conjecture for varieties that are not of abelian type.

`paper/full_attempt.tex` also proves that every abelian variety of Weil type
for Q(√−3) is, up to isogeny, a factor A × A′ of the Prym variety of an
étale triple cover, so that its Weil class is algebraic exactly when that of
the complement A′ is (its Theorem 8.2). A count of dimensions in the same
section indicates that this cannot reach the general member in dimension 8
or more, and the attempts to carry Schoen's construction to (F2) and (F3′)
lead back to instances of those statements.

## Layout

    book/main.tex           the book, standard book class
    book/chapters/          preface, seven chapters and the bibliography
    book/proposal.md        a draft Springer book proposal
    paper/weil_closure_attempt.tex
                            the research note
    paper/full_attempt.tex  an attempt at the conjecture in full: every
                            route, pushed as far as it goes, and the first
                            open statement on each
    paper/*.pdf, book/weil_classes_and_the_hodge_conjecture.pdf
                            the compiled papers and book
    verification/           Lean 4 and Julia checks of every finite step of
                            both papers (with a Python version of the Julia
                            checks); see verification/README.md
    H8/                     the author's earlier work, version 5.1.0
                            (doi:10.5281/zenodo.23227940), linked as a git
                            submodule; it holds the computations
    notes/hodge-residuals.md
                            what is still open, and why
    references.md           the Hodge-related reference library, by
                            journal or arXiv identifier

Clone with `git clone --recurse-submodules` to get `H8/` as well.

## Building

    cd book && latexmk -pdf main.tex
    cd paper && latexmk -pdf weil_closure_attempt.tex
    cd paper && latexmk -pdf full_attempt.tex

All three compile with pdflatex (TeX Live 2023) with no errors, undefined
references or overfull lines, and the compiled PDFs are in the repository.
The machine checks run with

    cd verification/lean && lake build
    julia verification/julia/checks.jl
    python3 verification/python/checks.py

No proof in the book or the papers depends on them. For submission to Springer, switch the book
to the `svmono` class, as the comment at the top of `book/main.tex` explains.
