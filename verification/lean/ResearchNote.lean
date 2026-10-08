/-
ResearchNote.lean

A check, by Lean 4's kernel, of the finite arithmetic behind the research note
"Closing the algebraic locus of Weil classes: an attempt and the exact point
where it stops" (paper/weil_closure_attempt.tex), and of one identity that
links it to Theorem 5.2 of paper/full_attempt.tex.

As with FullAttempt.lean, the geometry is not formalised: Lean's core library
has no Hodge theory. What is checked is this.

  * Section 1. Theorem 6 and Step 5 of Theorem 9 use an element τ = a + √-d
    of K = Q(√-d) for which τ/τ̄ is not a root of unity. A root of unity in an
    imaginary quadratic field has order dividing 4 or 6, so its 12th power is
    1. We check, by exact arithmetic in Z[√-d], that τ = 2 + √-d has
    τ^12 ≠ τ̄^12 for every squarefree d from 1 to 200, so for these d the
    element λ = τ/τ̄ is not a root of unity and λ^(2n) ≠ 1 for every n ≥ 1.
    The same is checked directly for 1 ≤ n ≤ 12 and squarefree d ≤ 50. We
    also record that d = 4 and d = 12, which are not squarefree, are the only
    d ≤ 200 where this τ fails.

  * Section 2. The U(1)-weights of Steps 2 and 5 of Theorem 9: the centre
    acts on the (a, b) summand by λ^(a-b), so a class is invariant only in
    the summands with a = b, and the Weil lines (2n, 0) and (0, 2n) are not
    among them.

  * Section 3. The two families of curves after Proposition 11: the genus of
    the cyclic triple cover of P^1 branched at 2n + 2 points (Riemann–Hurwitz),
    the dimensions n and n of its two eigenspaces of holomorphic forms
    (Chevalley–Weil), its 2n - 1 moduli against the n^2 of the Weil family,
    and the genus 3n + 1, eigenspace dimensions and 3n moduli of the etale
    triple covers.

  * Section 4. The identity 3 - (1 + σ + σ^2) = (1 - σ)(2 + σ), which shows
    that the map Ψ of Theorem 5.2 of the full attempt has the form required
    in Proposition 11 of the note.

Only the core library is used. No proof uses `sorry` or `native_decide`.
-/

namespace ResearchNote

/-! ## Section 1. τ/τ̄ is not a root of unity -/

/-- `x + y √-d`. -/
structure Zd where
  x : Int
  y : Int
deriving DecidableEq, Repr

/-- `(x + y√-d)(u + v√-d) = (xu - d yv) + (xv + yu)√-d`. -/
def Zd.mul (d : Int) (p q : Zd) : Zd := ⟨p.x * q.x - d * p.y * q.y, p.x * q.y + p.y * q.x⟩

def Zd.pow (d : Int) (p : Zd) : Nat → Zd
  | 0 => ⟨1, 0⟩
  | k + 1 => Zd.mul d p (Zd.pow d p k)

/-- `τ = 2 + √-d` and its conjugate `2 - √-d`. -/
def tau : Zd := ⟨2, 1⟩
def tauBar : Zd := ⟨2, -1⟩

/-- `d` has no square factor `k^2` with `k ≥ 2`. -/
def squarefree (d : Nat) : Bool :=
  (List.range (d + 1)).all (fun k => k < 2 || d % (k * k) != 0)

set_option maxRecDepth 100000 in
/-- `τ^12 ≠ τ̄^12` for every squarefree `d` from `1` to `200`. Since every root
of unity in an imaginary quadratic field has 12th power `1`, `τ/τ̄` is not a
root of unity, and so `(τ/τ̄)^(2n) ≠ 1` for every `n ≥ 1`. -/
theorem tau_not_root_of_unity :
    ∀ d : Nat, d < 201 → 1 ≤ d → squarefree d = true →
      Zd.pow (d : Int) tau 12 ≠ Zd.pow (d : Int) tauBar 12 := by
  decide

set_option maxRecDepth 100000 in
/-- The same, directly for the powers `2n` with `1 ≤ n ≤ 12`, for the
squarefree `d ≤ 50`. -/
theorem tau_power_direct :
    ∀ d : Nat, d < 51 → 1 ≤ d → squarefree d = true → ∀ n : Nat, n < 13 → 1 ≤ n →
      Zd.pow (d : Int) tau (2 * n) ≠ Zd.pow (d : Int) tauBar (2 * n) := by
  decide

/-- Squarefreeness matters: for `d = 4` and `d = 12`, where `Q(√-d)` is
`Q(i)` and `Q(√-3)`, the element `2 + √-d` is `2(1 + i)` or `2(1 + √-3)`, and
`τ/τ̄` is a root of unity. These are the only `d ≤ 200` where `2 + √-d` fails. -/
theorem tau_fails_when_not_squarefree :
    Zd.pow 4 tau 12 = Zd.pow 4 tauBar 12 ∧ Zd.pow 12 tau 12 = Zd.pow 12 tauBar 12 ∧
    squarefree 4 = false ∧ squarefree 12 = false := by
  decide

/-! ## Section 2. Weights in Theorem 9 -/

/-- The central `U(1)` acts on `∧^a V_σ ⊗ ∧^b V_σ̄` (any number of copies) by
`λ^(a-b)`; its exponent is `a - b`. -/
def weight (a b : Nat) : Int := (a : Int) - (b : Int)

/-- Step 2: the exponent vanishes exactly when `a = b`. -/
theorem weight_zero_iff (a b : Nat) : weight a b = 0 ↔ a = b := by
  unfold weight
  omega

/-- Step 5: the Weil lines have exponents `±2n ≠ 0`, while `η^n` has `0`. -/
theorem weil_lines_not_invariant (n : Nat) (hn : 1 ≤ n) :
    weight (2 * n) 0 ≠ 0 ∧ weight 0 (2 * n) ≠ 0 ∧ weight n n = 0 := by
  unfold weight
  omega

/-- Step 4: every element of `U` acts on the top degree `(2n, 2n)` of `A`, and
on the top degree `(2nm, 2nm)` of `A^m`, with exponent `0`. -/
theorem top_degree_fixed (n m : Nat) : weight (2 * n * m) (2 * n * m) = 0 := by
  unfold weight
  omega

/-! ## Section 3. The two families of curves -/

/-- Riemann–Hurwitz for a cyclic triple cover of `P^1` totally branched at
`2n + 2` points: `2g - 2 = 3(-2) + 2(2n + 2)`, so `g = 2n`. -/
theorem cyclic_cover_genus (n g : Int) (rh : 2 * g - 2 = 3 * (-2) + 2 * (2 * n + 2)) :
    g = 2 * n := by
  omega

/-- Chevalley–Weil for `y^3 = ∏_{i ≤ n+1} (x - a_i) ∏_{j ≤ n+1} (x - b_j)^2`.
For the character `k ∈ {1, 2}` the eigenspace of holomorphic forms has
dimension `-1 + ∑ ⟨k e / 3⟩` over the branch points, `e` the exponent there;
with `n + 1` exponents `1` and `n + 1` exponents `2`, three times the dimension
is `-3 + (n+1)(k mod 3) + (n+1)(2k mod 3)`. Both come out to `n`, and with the
invariant part (the forms on `P^1`, none) they add up to the genus `2n`. -/
theorem chevalley_weil (n d1 d2 : Int)
    (h1 : 3 * d1 = -3 + (n + 1) * 1 + (n + 1) * 2)
    (h2 : 3 * d2 = -3 + (n + 1) * 2 + (n + 1) * 1) :
    d1 = n ∧ d2 = n ∧ 0 + d1 + d2 = 2 * n := by
  omega

/-- The residues used above: `k mod 3` and `2k mod 3` for `k = 1, 2`. -/
theorem chevalley_weil_residues :
    (1 * 1) % 3 = 1 ∧ (1 * 2) % 3 = 2 ∧ (2 * 1) % 3 = 2 ∧ (2 * 2) % 3 = 1 := by
  decide

/-- The cyclic covers depend on `2n + 2` branch points up to the `3`-dimensional
`PGL_2`, so on `2n - 1` parameters, which is less than `n^2` for `n ≥ 2`. -/
theorem cyclic_family_small (n : Nat) (hn : 2 ≤ n) : 2 * n - 1 < n * n := by
  have := Nat.mul_le_mul_right n hn
  omega

/-- Etale triple covers of a curve of genus `n + 1`: the cover has genus
`3(n+1) - 2 = 3n + 1`; the forms split as `n + 1` invariant ones and `n` in
each nontrivial eigenspace; the Prym variety has dimension `2n`. -/
theorem etale_family (n gC e : Nat)
    (rh : 2 * gC + 4 = 6 * (n + 1)) (split : gC = (n + 1) + 2 * e) :
    gC = 3 * n + 1 ∧ e = n ∧ gC - (n + 1) = 2 * n := by
  omega

/-- The etale family has `3n` moduli; this is at least `n^2` exactly when
`n ≤ 3`. -/
theorem etale_family_fills (n : Nat) : n * n ≤ 3 * n ↔ n ≤ 3 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have h4 : 4 ≤ n := by omega
    have := Nat.mul_le_mul_right n h4
    omega
  · intro h
    exact Nat.mul_le_mul_right n h

/-! ## Section 4. The map Ψ of the full attempt -/

/-- `P = 3 - N = 3 - (1 + σ + σ^2)` factors as `(1 - σ)(2 + σ)`, as a
polynomial identity in `σ`. So `Ψ(c) = P(∑ (c_i - c_0)) = (1 - σ) ∑ ψ_i(AJ(c_i))`
with every `ψ_i = 2 + σ ∈ Z[σ]`, which is the form of Proposition 11. -/
theorem prym_projector (σ : Int) : 3 - (1 + σ + σ * σ) = (1 - σ) * (2 + σ) := by
  simp only [Int.sub_mul, Int.mul_add, Int.one_mul]
  omega

end ResearchNote

/-! ## Axioms -/

#print axioms ResearchNote.tau_not_root_of_unity
#print axioms ResearchNote.tau_power_direct
#print axioms ResearchNote.weil_lines_not_invariant
#print axioms ResearchNote.chevalley_weil
#print axioms ResearchNote.etale_family
#print axioms ResearchNote.etale_family_fills
#print axioms ResearchNote.prym_projector
