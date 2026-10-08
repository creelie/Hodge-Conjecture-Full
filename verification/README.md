# Machine checks

These files check by machine every finite step of the two papers in
`paper/`:

- `full_attempt.tex`, the attempt at the Hodge conjecture in full;
- `weil_closure_attempt.tex`, the research note.

The arithmetic of H8 is checked by H8's own Lean file
(`H8/lean/HodgeObstruction.lean`).

No proof in either paper depends on a computer. These checks also do not
reach three things:

- the geometry the papers rely on (the Hodge decomposition, hard Lefschetz,
  the theorems of Schoen, Bloch, Looijenga and André, and those of H8);
- the infinite statements of the note: the countability of the locus, its
  density, and the dichotomy;
- the open questions on which the papers stop, Question 5.4 of the full
  attempt above all;
- the dimension count of Remark 8.4 of the full attempt as an argument.
  Lean checks its arithmetic for every m and k, but the remark rests on an
  expected-dimension heuristic and is not a proof.

No proof assistant today has the Hodge theory needed to state those
theorems, let alone check them. The Hodge conjecture is not proved here.

## Lean 4

Checked by Lean's kernel with the core library only (no Mathlib), toolchain
`leanprover/lean4:v4.34.0`, the same as H8. Neither file uses `sorry` or
`native_decide`. Each file ends by printing the axioms of its main
theorems. They are at most `propext`, `Classical.choice` and `Quot.sound`,
the standard ones.

### `lean/FullAttempt.lean`: the full attempt

| Lean theorem | Paper |
| --- | --- |
| `hard_lefschetz_step`, `hard_lefschetz_degree` | Proposition 2.2 |
| `small_dimension_indices` | Corollary 2.3 |
| `descent` | Proposition 2.4 |
| `middle_degree` (the Lefschetz standard conjecture is the hypothesis `lefschetzB`) | Proposition 2.5 |
| `etale_triple_genus`, `prym_dimension`, `eigenspace_dimension`, `lambda_middle_degree` | Section 5.4, set-up of Theorem 5.2 |
| `psi_square` | Theorem 5.2, Step 2 |
| `prym_locus_proper`, `prym_locus_sixfold` | Section 5.4 and Question 5.4 (3n against n²) |
| `jacobian_locus_proper` | the analogy after Question 5.4 (3g − 3 against g(g+1)/2) |
| `zeta_primitive`, `chi_hom`, `chi_conj`, `chi_orthogonal` | Theorem 5.2, Steps 1 and 3 |
| `z_push_eigen`, `step3_isotypic`, `q0_decomposition`, `step3_eigenvalues`, `eigen_pairing_vanishes` | Theorem 5.2, Step 3 |
| `two_plus_sigma_isogeny` | the remark after Question 5.4 |
| `step5_weights`, `eta_kills_weil`, `step5_w_nonzero`, `step5_c_positive` | Theorem 5.2, Step 5 |
| `transfer_dimensions`, `complement_weil_type` | Theorem 8.2: dim B = 2(g − 1) = dim A + dim A′, and A′ is of Weil type |
| `alpha_prym` | Theorem 8.2: 1 + ζ + ζ² = 0, so α ∘ P = 3α |
| `twothree_degrees` | Lemma 8.1: ω₂ ∪ ω₂ = 0, and the push-forward lands in the degree of W(A₁) |
| `block_moduli`, `square_expand`, `count_fails`, `count_three`, `count_two` | Remark 8.4: no k passes once m ≥ 4, only k = 0 at m = 3, exactly k ≤ 2 at m = 2 |

In Propositions 2.2, 2.4 and 2.5 the geometric facts are hypotheses: hard
Lefschetz, the projection formula, and the compatibility of push-forward
with cycle classes. Lean checks that the conclusions follow from them, not
the facts themselves.

### `lean/ResearchNote.lean`: the research note

| Lean theorem | Note |
| --- | --- |
| `tau_not_root_of_unity`, `tau_power_direct`, `tau_fails_when_not_squarefree` | Theorem 6 and Theorem 9, Step 5: τ = 2 + √−d, τ¹² ≠ τ̄¹² for squarefree d ≤ 200 |
| `weight_zero_iff`, `weil_lines_not_invariant`, `top_degree_fixed` | Theorem 9, Steps 2, 4 and 5 |
| `cyclic_cover_genus`, `chevalley_weil`, `chevalley_weil_residues`, `cyclic_family_small` | the cyclic triple covers of P¹ after Proposition 11 |
| `etale_family`, `etale_family_fills` | the étale triple covers after Proposition 11 |
| `prym_projector` | the remark after Question 5.4 of the full attempt: 3 − (1 + σ + σ²) = (1 − σ)(2 + σ) |

For `tau_not_root_of_unity`: every root of unity in an imaginary quadratic
field has twelfth power 1, so τ¹² ≠ τ̄¹² shows that τ/τ̄ is not a root of
unity. The check is limited to squarefree d because for d = 4 and d = 12,
the only failures up to 200, the element 2 + √−d is 2(1 + i) or 2(1 + √−3).
The note only asks for some τ, and these d give no new fields.

Run:

    cd verification/lean
    lake build

## Julia: `julia/checks.jl`, and its Python version `python/checks.py`

Base Julia, no packages. Everything is exact: integers, `Rational{BigInt}`,
and pairs of integers for `Z[ζ]`. The Python file performs the same checks
in the same order, and `expected_output.txt` is its output (102 checks).

Full attempt:

1. Dimension counts: 3n against n² for n ≤ 12, and 3g − 3 against
   g(g+1)/2 for g ≤ 12.
2. Hodge classes on a general abelian variety of Weil type of dimension 2n,
   for n = 1, 2, 3, 4.
   - These are the invariants of sl(2n), the complexified Hodge group, in
     the exterior algebra of V ⊕ V*. They are computed as the weight-zero
     vectors killed by the simple raising operators, with an exact rank.
   - Result: one line in every even degree except the middle one, which has
     three (ηⁿ and the two Weil lines). Odd degrees have none.
   - Also checked: η is invariant; η ∪ ω = ηⁿ ∪ ω = ηⁿ ∪ ω̄ = 0; and η²ⁿ ≠ 0
     and ω ∪ ω̄ ≠ 0 (Step 5 of Theorem 5.2). The sign printed for η²ⁿ comes
     from the order of the basis, not from the complex orientation.
3. Schoen's Lemma 1.2 as used in Step 1: the part U_χ of H^h(C^h)^{G'} on
   which δ* acts by χ(1) is one-dimensional. Two methods:
   - for g = 3 (h = 4), project every monomial by summing over the whole
     group (Z/3)⁴ ⋊ S₄ of 1944 elements, with Koszul signs;
   - for g = 3 and g = 4 (h = 6), use the stabilizer of each monomial.
4. Steps 1 and 2, for h = 2, 4 and 6:
   - u_χ has h! terms, all ±1;
   - it is fixed by the permutations of the factors;
   - its integral against u_χ̄ over C^h is ±h!, so it is nonzero.

   For h = 4 the one projection found in item 3 is 81 times u_χ.

Research note, Theorem 9:

5. Step 1: the endomorphisms of V^m ⊕ V*^m commuting with sl(2n) span
   2m² dimensions (M_m(K)) for 2n = 4, 6 and m = 1, 2. For 2n = 2 they span
   4m², because the standard representation of SL₂ is self-dual. That is why
   the note assumes 2n ≥ 3.
6. Step 3: the sl(2n)-invariants in degree 2 on A^m, for 2n = 4, 6 and
   m = 1, 2, 3, are m² classes of type (1,1) and none of type (2,0) or
   (0,2). For 2n = 2 there are m(m+1)/2 of each of the types (2,0) and
   (0,2) as well. Here the invariants are computed as the common kernel of
   all the Chevalley generators, with no weight argument.

Full attempt, Section 8:

7. Lemma 8.1 for 2m₁, 2m₂ ∈ {2, 4}, in the exterior algebra of
   H¹(A₁ × A₂): ω₂ ∪ ω₂ = 0; ω₂ ∪ ω̄₂ is a nonzero multiple p of the top
   class of A₂; the top power of V_χ(A₁) ⊕ V_χ(A₂) is ω₁ ∪ ω₂; and
   pr₁*(x ∪ pr₂*γ) = p(s t̄ ω₁ + s̄ t ω̄₁), computed on the four products of
   basis classes. Corollary 8.3 for k ≤ 4: on E^k × Ē^k, ω_χ is
   (−1)^(k(k−1)/2) times the product of the classes dz_i ∧ dz̄_(k+i). Remark
   8.4 for 2 ≤ m ≤ 12 and k ≤ 12: the k with 3(m + k) + 3k ≥ (m + k)² are
   0, 1, 2 for m = 2, only 0 for m = 3, and none from m = 4 on.

Run either:

    julia verification/julia/checks.jl
    python3 verification/python/checks.py

Both should print `all checks passed`.

## What was run where

- Both Lean files were built with Lean 4.34.0, and every theorem checked.
- The Python checks were run, and all 102 passed (`expected_output.txt`).
- The Julia file was run with Julia 1.11.7 on commit b91b573: all 75 checks
  it then held passed, and its output matched `expected_output.txt` line for
  line, apart from `true`/`false` in place of Python's `True`/`False`.
- Part 7 was added after that run. It has been run in Python, and the Julia
  version parses without syntax errors and mirrors it one for one, but it
  has not yet been run in Julia.
