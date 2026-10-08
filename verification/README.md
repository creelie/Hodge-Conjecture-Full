# Machine checks for `paper/full_attempt.tex`

No proof in the paper depends on a computer. These files repeat the finite
parts of its arguments by machine. They do not touch the geometry the paper
relies on (the theorems of Schoen, Bloch, Looijenga and André, and those of
H8), and none of them bears on Question 5.4, the open question on which the
Weil route stops. The Hodge conjecture is not proved here.

## Lean 4: `lean/FullAttempt.lean`

Checked by Lean's kernel, core library only (no Mathlib), toolchain
`leanprover/lean4:v4.34.0`, the same as H8. No `sorry`, no `native_decide`.
The file ends by printing the axioms of its main theorems. They are at most
`propext`, `Classical.choice` and `Quot.sound`, the standard ones.

| Lean theorem | Paper |
| --- | --- |
| `hard_lefschetz_step`, `hard_lefschetz_degree` | Proposition 2.2 |
| `small_dimension_indices` | Corollary 2.3 |
| `descent` | Proposition 2.4 |
| `middle_degree` (the Lefschetz standard conjecture is the hypothesis `lefschetzB`) | Proposition 2.5 |
| `etale_triple_genus`, `prym_dimension`, `eigenspace_dimension`, `lambda_middle_degree` | Section 5.4, set-up of Theorem 5.2 |
| `psi_square` | Theorem 5.2, Step 2 |
| `prym_locus_proper`, `prym_locus_sixfold` | Section 5.4, Question 5.4 (3n against n²) |
| `jacobian_locus_proper` | the analogy after Question 5.4 (3g − 3 against g(g+1)/2) |
| `zeta_primitive`, `chi_hom`, `chi_conj`, `chi_orthogonal` | Theorem 5.2, Steps 1 and 3 |
| `z_push_eigen`, `step3_isotypic`, `q0_decomposition`, `step3_eigenvalues`, `eigen_pairing_vanishes` | Theorem 5.2, Step 3 |
| `step5_weights`, `eta_kills_weil`, `step5_w_nonzero`, `step5_c_positive` | Theorem 5.2, Step 5 |

In Propositions 2.2, 2.4 and 2.5 the geometric facts (hard Lefschetz, the
projection formula, the compatibility of push-forward with cycle classes)
are hypotheses. Lean checks that the conclusions follow from them, not the
facts themselves.

Run:

    cd verification/lean
    lake build

## Julia: `julia/checks.jl`, and its Python version `python/checks.py`

Base Julia, no packages. Everything is exact (integers, `Rational{BigInt}`,
and pairs of integers for `Z[ζ]`). The Python file performs the same checks
in the same order, and `expected_output.txt` is its output.

1. Dimension counts: 3n against n² for n ≤ 12, and 3g − 3 against
   g(g+1)/2 for g ≤ 12.
2. Hodge classes on a general abelian variety of Weil type of dimension 2n,
   for n = 1, 2, 3, 4. These are the invariants of sl(2n), the complexified
   Hodge group, in the exterior algebra of V ⊕ V*. They are computed as the
   weight-zero vectors killed by the simple raising operators, with an exact
   rank. The result is one line in every even degree except the middle one,
   which has three: ηⁿ and the two Weil lines. Odd degrees have none. Also
   checked: η is invariant, η ∪ ω = ηⁿ ∪ ω = ηⁿ ∪ ω̄ = 0, and η²ⁿ ≠ 0 and
   ω ∪ ω̄ ≠ 0 (Step 5 of Theorem 5.2). The sign printed for η²ⁿ comes from the
   order of the basis, not from the complex orientation.
3. Schoen's Lemma 1.2 as used in Step 1: the part U_χ of H^h(C^h)^{G'} on
   which δ* acts by χ(1) is one-dimensional. Two methods are used:
   - For g = 3 (h = 4), project every monomial by summing over the whole
     group (Z/3)⁴ ⋊ S₄ of 1944 elements, with Koszul signs.
   - For g = 3 and g = 4 (h = 6), use the stabilizer of each monomial.
4. Steps 1 and 2, for h = 2, 4 and 6: u_χ has h! terms, all ±1. It is fixed
   by the permutations of the factors. Its integral against u_χ̄ over C^h is
   ±h!, so it is nonzero. For h = 4 the one projection found in item 3 is 81
   times u_χ.

Run either:

    julia verification/julia/checks.jl
    python3 verification/python/checks.py

Both should print `all checks passed`.

## What was run where

- The Lean file was built with Lean 4.34.0, and every theorem checked.
- The Python checks were run, and all passed (`expected_output.txt`).
- The Julia file has not been run yet. The environment where these files
  were prepared could not download Julia. It parses without syntax errors and
  mirrors the Python checks one for one. Running it once and comparing with
  `expected_output.txt` is the remaining step. The only expected difference
  is `true`/`false` in place of Python's `True`/`False`.
