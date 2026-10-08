/-
FullAttempt.lean

A check, by Lean 4's kernel, of the finite arithmetic and the bare
deductions behind "The Hodge conjecture: an attempt in full, and the
statements at which it stops" (paper/full_attempt.tex).

Nothing here proves the Hodge conjecture, and nothing here could: Lean's
core library has no Hodge theory, and the geometric inputs of the paper
(the Hodge decomposition, hard Lefschetz, Schoen's theorem, Bloch's
semiregularity theorem, Looijenga's monodromy computation, Andre's theorem
and the results of H8) are not formalised. What is checked is this.

  * Section 1. The deductions of Propositions 2.2, 2.4 and 2.5 and of
    Corollary 2.3, with every geometric fact they use stated as a named
    hypothesis. The Lefschetz standard conjecture appears as the hypothesis
    `lefschetzB` of `middle_degree`, so the file shows exactly where that
    reduction depends on it.

  * Section 2. The counting of genera and dimensions in Section 5 of the
    paper, for every genus at once: the genus of an etale triple cover, the
    dimension of the Prym variety and of the eigenspaces of the covering
    automorphism, the squareness of the differential in Step 2 of
    Theorem 5.2, and the comparison of the 3n moduli of (X, L) with the n^2
    moduli of the Weil family, and of the 3g - 3 moduli of curves with the
    g(g+1)/2 moduli of abelian varieties used in the analogy after
    Question 5.4.

  * Section 3. Exact arithmetic in Z[zeta], zeta a primitive cube root of
    unity: the characters of Z/3, their orthogonality, and the isotypic
    bookkeeping of Step 3 of Theorem 5.2, including the fact that the part of
    Schoen's class on which delta^* acts by chi(1) is z_{chi-bar}, and the
    cancellation that makes a pairing between eigenvectors vanish.

  * Section 4. The U(1)-weight count of Step 5 of Theorem 5.2 and the
    deduction of c > 0 and w /= 0 from it.

  * Section 5. Section 8 of the paper: the dimensions in Theorem 8.2 (the
    Prym variety B of dimension 2(g - 1) splits up to isogeny as A x A' with
    A' of dimension 2(g - 1 - m), and the eigenspaces of A' have equal
    dimension g - 1 - m, so A' is of Weil type); the identity
    alpha o P = 3 alpha in Z[zeta]; the bidegree facts behind Lemma 8.1; and
    the count of Remark 8.4 for every m and k at once: once m >= 4 no
    complement with at most 3k moduli passes, at m = 3 only k = 0 does, and
    at m = 2 exactly k <= 2 do. The count is a heuristic in the paper, and
    Lean checks only its arithmetic.

Only the core library is used. No proof uses `sorry` or `native_decide`;
`decide` is evaluated by the kernel. Section 6 prints the axioms of the main
theorems.
-/

namespace FullAttempt

/-! ## Section 1. The reductions of Section 2 as deductions -/

section Reductions

/-- Proposition 2.2. `Hp` and `Hq` stand for `H^{2p}(X,Q)` and
`H^{2n-2p}(X,Q)`, `L` for cup product with `h^{n-2p}`. The hypotheses are the
hard Lefschetz theorem together with Hodge type (`L` maps the Hodge classes
onto the Hodge classes), and the fact that cutting with hyperplanes preserves
algebraic classes. -/
theorem hard_lefschetz_step {Hp Hq : Type}
    (HdgP AlgP : Hp → Prop) (HdgQ AlgQ : Hq → Prop) (L : Hp → Hq)
    (L_onto_hodge : ∀ β, HdgQ β → ∃ α, HdgP α ∧ L α = β)
    (L_alg : ∀ α, AlgP α → AlgQ (L α))
    (hcP : ∀ α, HdgP α → AlgP α) :
    ∀ β, HdgQ β → AlgQ β := by
  intro β hβ
  obtain ⟨α, hα, rfl⟩ := L_onto_hodge β hβ
  exact L_alg α (hcP α hα)

/-- The degree bookkeeping of Proposition 2.2: `L^{n-2p}` carries degree `2p`
to degree `2n-2p`. -/
theorem hard_lefschetz_degree (n p : Nat) (hp : 2 * p ≤ n) :
    2 * p + 2 * (n - 2 * p) = 2 * n - 2 * p := by
  omega

/-- Corollary 2.3, the index count: when `dim X ≤ 3` every degree `p` is one
of `0, 1, n-1, n`. -/
theorem small_dimension_indices :
    ∀ n p : Nat, n ≤ 3 → p ≤ n → p = 0 ∨ p = 1 ∨ p = n - 1 ∨ p = n := by
  intro n p hn hp
  omega

/-- Proposition 2.4. `HX` and `HY` stand for `H^{2p}(X,Q)` and
`H^{2(p+r)}(Y,Q)`; `pullCup` is `α ↦ f^*α ∪ h_Y^r`, `push` is `f_*`, and
`scale` is multiplication by the positive integer `d = f_*(h_Y^r)`. -/
theorem descent {HX HY : Type}
    (HdgX AlgX : HX → Prop) (HdgY AlgY : HY → Prop)
    (pullCup : HX → HY) (push : HY → HX) (scale : HX → HX)
    (pullCup_hodge : ∀ α, HdgX α → HdgY (pullCup α))
    (push_alg : ∀ β, AlgY β → AlgX (push β))
    (projection_formula : ∀ α, push (pullCup α) = scale α)
    (unscale : ∀ α, AlgX (scale α) → AlgX α)
    (hcY : ∀ β, HdgY β → AlgY β) :
    ∀ α, HdgX α → AlgX α := by
  intro α hα
  apply unscale
  rw [← projection_formula]
  exact push_alg _ (hcY _ (pullCup_hodge α hα))

/-- Proposition 2.5. `restrict` is `i^*`, `gysin` is `i_*`, `Lpow` is
`L^{n-2p}` and `Linv` its inverse. The hypothesis `lefschetzB` is the
Lefschetz standard conjecture: the inverse is induced by an algebraic
correspondence, so it maps algebraic classes to algebraic classes. -/
theorem middle_degree {HX HY : Type}
    (HdgX AlgX : HX → Prop) (HdgY AlgY : HY → Prop)
    (res : HX → HY) (gysin : HY → HX) (Lpow Linv : HX → HX)
    (res_hodge : ∀ α, HdgX α → HdgY (res α))
    (gysin_alg : ∀ β, AlgY β → AlgX (gysin β))
    (gysin_res : ∀ α, gysin (res α) = Lpow α)
    (inverse : ∀ α, Linv (Lpow α) = α)
    (lefschetzB : ∀ γ, AlgX γ → AlgX (Linv γ))
    (hcY : ∀ β, HdgY β → AlgY β) :
    ∀ α, HdgX α → AlgX α := by
  intro α hα
  have h1 : AlgX (Lpow α) := by
    rw [← gysin_res]
    exact gysin_alg _ (hcY _ (res_hodge α hα))
  have h2 := lefschetzB _ h1
  rwa [inverse] at h2

end Reductions

/-! ## Section 2. Genera and dimensions in Section 5 -/

section Counting

/-- Riemann–Hurwitz for an etale cover of degree three, `2 g_C - 2 = 3 (2g - 2)`,
written without subtraction as `2 g_C + 4 = 6 g`, gives `g_C = 3g - 2`. -/
theorem etale_triple_genus (g gC : Nat) (hg : 1 ≤ g) (rh : 2 * gC + 4 = 6 * g) :
    gC = 3 * g - 2 := by
  omega

/-- The Prym variety `B = P(J)` has dimension `g_C - g = 2g - 2 = 2n`, where
`n = g - 1`. -/
theorem prym_dimension (g gC : Nat) (hg : 2 ≤ g) (rh : 2 * gC + 4 = 6 * g) :
    gC - g = 2 * (g - 1) := by
  omega

/-- `H^1(C)` splits under the covering automorphism into the invariant part,
of dimension `2g`, and two conjugate eigenspaces of equal dimension `e`. Then
`e = 2g - 2 = h`, the number of factors of `C^h` in the proof of
Theorem 5.2. -/
theorem eigenspace_dimension (g gC e : Nat) (hg : 2 ≤ g)
    (rh : 2 * gC + 4 = 6 * g) (split : 2 * gC = 2 * g + 2 * e) :
    e = 2 * g - 2 := by
  omega

/-- Step 2 of Theorem 5.2: the holomorphic 1-forms of `B`, which are the forms
of `C` in the nontrivial eigenspaces, number `g_C - g`, and the map `Ψ` has
`h = 2g - 2` source dimensions; the two agree, so the differential is
square. -/
theorem psi_square (g gC : Nat) (hg : 2 ≤ g) (rh : 2 * gC + 4 = 6 * g) :
    gC - g = 2 * g - 2 := by
  omega

/-- `Λ` has dimension `n` inside `C^h`, `h = 2n`, so its class lies in degree
`2(h - n) = 2n`, the middle degree of the `2n`-dimensional `B`. -/
theorem lambda_middle_degree (n : Nat) : 2 * (2 * n - n) = 2 * n := by
  omega

/-- Pairs `(X, L)` with `g(X) = n + 1` have `3g - 3 = 3n` moduli and the split
Weil family of dimension `2n` has `n^2`. The Prym locus is a proper subset of
the family exactly when `n ≥ 4`. -/
theorem prym_locus_proper (n : Nat) : 3 * n < n * n ↔ 4 ≤ n := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have hle : n ≤ 3 := by omega
    have := Nat.mul_le_mul_right n hle
    omega
  · intro hn
    have := Nat.mul_le_mul_right n hn
    omega

/-- At `n = 3` the two dimensions agree, so the Prym family can fill the split
sixfold family; the count alone does not show that it does. -/
theorem prym_locus_sixfold : 3 * 3 = 3 * 3 := rfl

/-- The analogy after Question 5.4: curves of genus `g ≥ 2` have `3g - 3`
moduli and principally polarized abelian varieties of dimension `g` have
`g(g+1)/2`; the Jacobian locus is proper exactly when `g ≥ 4`. Both sides are
doubled to avoid division. -/
theorem jacobian_locus_proper (g : Nat) (hg : 2 ≤ g) :
    2 * (3 * g - 3) < g * (g + 1) ↔ 4 ≤ g := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have h23 : g = 2 ∨ g = 3 := by omega
    rcases h23 with rfl | rfl <;> simp at h
  · intro hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_mul, Nat.mul_add]
    omega

end Counting

/-! ## Section 3. Characters of Z/3 in Z[ζ] -/

/-- `a + b ζ` with `ζ^2 = -1 - ζ`. -/
structure Zz where
  a : Int
  b : Int
deriving DecidableEq, Repr

namespace Zz

def zero : Zz := ⟨0, 0⟩
def one : Zz := ⟨1, 0⟩
def zeta : Zz := ⟨0, 1⟩
def three : Zz := ⟨3, 0⟩
def add (x y : Zz) : Zz := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : Zz) : Zz := ⟨-x.a, -x.b⟩
def sub (x y : Zz) : Zz := add x (neg y)
/-- `(a + bζ)(c + dζ) = (ac - bd) + (ad + bc - bd)ζ`. -/
def mul (x y : Zz) : Zz := ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a - x.b * y.b⟩
def pow (x : Zz) : Nat → Zz
  | 0 => one
  | k + 1 => mul x (pow x k)
/-- Complex conjugation, `ζ ↦ ζ^2 = -1 - ζ`. -/
def conj (x : Zz) : Zz := ⟨x.a - x.b, -x.b⟩

end Zz

open Zz

/-- `ζ` is a primitive cube root of unity. -/
theorem zeta_primitive :
    pow zeta 3 = one ∧ zeta ≠ one ∧ pow zeta 2 ≠ one ∧
    add one (add zeta (pow zeta 2)) = zero ∧ conj zeta = pow zeta 2 := by
  decide

/-- The character `χ_k` of `Z/3`, `t ↦ ζ^{kt}`. -/
def chi (k t : Nat) : Zz := pow zeta (k * t)

/-- `-t` in `Z/3`, for `t < 3`. -/
def negZ3 (t : Nat) : Nat := (3 - t) % 3

/-- Each `χ_k` is a homomorphism, read modulo 3. In Step 1 of Theorem 5.2 this
is why `σ^{v_1} × ⋯ × σ^{v_h}` multiplies `u_χ` by `χ(∑ v_i)`. -/
theorem chi_hom : ∀ k, k < 3 → ∀ s, s < 3 → ∀ t, t < 3 →
    chi k ((s + t) % 3) = mul (chi k s) (chi k t) := by
  decide

/-- `χ_2 = \bar χ_1` and `\bar χ_1 (t) = χ_1(-t)`. -/
theorem chi_conj : ∀ t, t < 3 →
    conj (chi 1 t) = chi 2 t ∧ conj (chi 1 t) = chi 1 (negZ3 t) := by
  decide

/-- Orthogonality: `∑_t χ_k(t) χ_l(-t) = 3` if `k = l` and `0` otherwise. -/
theorem chi_orthogonal : ∀ k, k < 3 → ∀ l, l < 3 →
    add (mul (chi k 0) (chi l (negZ3 0)))
      (add (mul (chi k 1) (chi l (negZ3 1))) (mul (chi k 2) (chi l (negZ3 2))))
    = (if k = l then three else zero) := by
  decide

/-- A class on the three components `Q_0, Q_1, Q_2`, as its three
coefficients. -/
structure Tri where
  x0 : Zz
  x1 : Zz
  x2 : Zz
deriving DecidableEq, Repr

namespace Tri

def add (u v : Tri) : Tri := ⟨Zz.add u.x0 v.x0, Zz.add u.x1 v.x1, Zz.add u.x2 v.x2⟩
def smul (c : Zz) (u : Tri) : Tri := ⟨mul c u.x0, mul c u.x1, mul c u.x2⟩
/-- `δ_*`, which carries `Q_t` to `Q_{t+1}`. -/
def push (u : Tri) : Tri := ⟨u.x2, u.x0, u.x1⟩
/-- `δ^* = (δ^{-1})_*`. -/
def pull (u : Tri) : Tri := push (push u)
/-- `[Q_0]`. -/
def q0 : Tri := ⟨one, zero, zero⟩
/-- Schoen's `z_χ = ∑_t χ(-t) δ^t_* Q_0` for `χ = χ_k`. -/
def z (k : Nat) : Tri := ⟨chi k (negZ3 0), chi k (negZ3 1), chi k (negZ3 2)⟩
/-- `∑_t c(t) δ^t_* u`. -/
def avg (c : Nat → Zz) (u : Tri) : Tri :=
  add (smul (c 0) u) (add (smul (c 1) (push u)) (smul (c 2) (push (push u))))

end Tri

open Tri

/-- `δ^*` and `δ_*` are inverse to each other. -/
theorem pull_push : ∀ u : Tri, Tri.pull (Tri.push u) = u ∧ Tri.push (Tri.pull u) = u := by
  intro u
  cases u
  exact ⟨rfl, rfl⟩

/-- `z_χ` is an eigenvector of `δ_*` with eigenvalue `χ(1)`. -/
theorem z_push_eigen : ∀ k, k < 3 → Tri.push (z k) = Tri.smul (chi k 1) (z k) := by
  decide

/-- Step 3 of Theorem 5.2: the part of `[Q_0]` on which `δ^*` acts by `χ(1)`
is a third of `∑_t χ(t) δ^t_*[Q_0]`, and that sum is Schoen's `z_{\bar χ}`. -/
theorem step3_isotypic :
    Tri.avg (chi 1) q0 = z 2 ∧
    Tri.pull (z 2) = Tri.smul (chi 1 1) (z 2) ∧
    z 2 ≠ ⟨zero, zero, zero⟩ := by
  decide

/-- The three isotypic parts of `[Q_0]` add up to `3 [Q_0]`. -/
theorem q0_decomposition :
    Tri.add (z 0) (Tri.add (z 1) (z 2)) = Tri.smul three q0 := by
  decide

/-- In `Z[ζ]`, multiplication by `ζ` or `ζ^2` fixes only `0`. -/
theorem fixed_by_zeta_power (m : Nat) (hm : m = 1 ∨ m = 2) (p : Zz)
    (h : mul (pow zeta m) p = p) : p = zero := by
  have h1 : pow zeta 1 = ⟨0, 1⟩ := by decide
  have h2 : pow zeta 2 = ⟨-1, -1⟩ := by decide
  cases p with
  | mk a b =>
    rcases hm with rfl | rfl
    · rw [h1] at h
      simp only [mul, Zz.mk.injEq] at h
      simp only [zero, Zz.mk.injEq]
      omega
    · rw [h2] at h
      simp only [mul, Zz.mk.injEq] at h
      simp only [zero, Zz.mk.injEq]
      omega

/-- The vanishing used in Steps 3 and 5: if an automorphism preserves a
pairing, `x` and `y` are eigenvectors with eigenvalues `α` and `β`, and
`αβ` is `ζ` or `ζ^2`, then `⟨x, y⟩ = 0`. -/
theorem eigen_pairing_vanishes {V : Type} (pair : V → V → Zz) (δ : V → V)
    (smulV : Zz → V → V) (x y : V) (α β : Zz) (m : Nat) (hm : m = 1 ∨ m = 2)
    (invariant : pair (δ x) (δ y) = pair x y)
    (hx : δ x = smulV α x) (hy : δ y = smulV β y)
    (bilinear : pair (smulV α x) (smulV β y) = mul (mul α β) (pair x y))
    (hαβ : mul α β = pow zeta m) :
    pair x y = zero := by
  apply fixed_by_zeta_power m hm
  rw [← hαβ, ← bilinear, ← hx, ← hy, invariant]

/-- The eigenvalue products that occur in Step 3: a class on which `δ^*` acts
by `ψ(1)` is paired with `u_{\bar χ}`, on which it acts by `\bar χ(1)`; the
product is `1` for `ψ = χ` and a primitive cube root of unity otherwise. -/
theorem step3_eigenvalues :
    mul (chi 1 1) (chi 2 1) = one ∧
    mul (chi 0 1) (chi 2 1) = pow zeta 2 ∧
    mul (chi 2 1) (chi 2 1) = pow zeta 1 := by
  decide

/-- After Question 5.4: on the part of `J` where `1 + σ + σ^2 = 0`, the product
`(2 + σ)(2 + σ^2)` is `3`, so `2 + σ` is an isogeny there and
`(1 - σ)(J) = (1 - σ)(2 + σ)(J) = B`. In `Z[ζ]` this is the norm
`(2 + ζ)(2 + ζ^2) = 3`. -/
theorem two_plus_sigma_isogeny :
    mul (Zz.add ⟨2, 0⟩ zeta) (Zz.add ⟨2, 0⟩ (pow zeta 2)) = three := by
  decide

/-! ## Section 4. Step 5 of Theorem 5.2 -/

section Step5

/-- The weight of the central `U(1)` on `∧^a V_χ ⊗ ∧^b V_{\bar χ}` is `a - b`.
-/
def weight (a b : Nat) : Int := (a : Int) - (b : Int)

/-- `η` has bidegree `(1,1)`, so `η^n` has bidegree `(n,n)`; the Weil lines
have bidegrees `(2n,0)` and `(0,2n)`; the orientation class has `(2n,2n)`.
For `n ≥ 1` the products `η^n ∪ w` have weight `±2n ≠ 0`, while the
orientation class has weight `0`, so these products integrate to zero. -/
theorem step5_weights (n : Nat) (hn : 1 ≤ n) :
    weight n n = 0 ∧ weight (2 * n) (2 * n) = 0 ∧
    weight n n + weight (2 * n) 0 ≠ weight (2 * n) (2 * n) ∧
    weight n n + weight 0 (2 * n) ≠ weight (2 * n) (2 * n) := by
  unfold weight
  omega

/-- `η ∪ ω_χ = 0`: its bidegree would be `(2n+1, 1)`, and `V_χ` has dimension
`2n`. -/
theorem eta_kills_weil (n : Nat) : ¬ (2 * n + 1 ≤ 2 * n) := by
  omega

/-- The end of Step 5. With `cl(Y) = c η^n + w`: pairing with a Weil class
`ω̄` kills `η^n`, so a nonzero pairing of `cl(Y)` with `ω̄` forces
`w ≠ 0`. -/
theorem step5_w_nonzero {V : Type} (zeroV : V) (φ : V → Zz)
    (φ_zero : φ zeroV = zero) (clY etaN w : V) (c : Zz)
    (linear : φ clY = Zz.add (mul c (φ etaN)) (φ w))
    (eta_orth : φ etaN = zero)
    (pairs : φ clY ≠ zero) : w ≠ zeroV := by
  intro hw
  apply pairs
  rw [linear, eta_orth, hw, φ_zero]
  cases c
  simp [mul, Zz.add, zero]

/-- And pairing with `η^n` gives `c > 0`: the degree of `Y` equals
`c ∫ η^{2n}`, both are positive, and `c` is scaled to an integer. -/
theorem step5_c_positive (c deg vol : Int) (hdeg : 0 < deg) (hvol : 0 < vol)
    (h : deg = c * vol) : 0 < c := by
  apply Classical.byContradiction
  intro hc
  have hc' : c ≤ 0 := by omega
  have : c * vol ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hc' (by omega)
  omega

end Step5

/-! ## Section 5. Section 8: the transfer and the count -/

section Spread

/-- Theorem 8.2, the dimensions. The curve `C` is an etale triple cover of `X`
of genus `g`, so `g_C = 3g - 2` and the Prym variety `B` has dimension
`g_C - g = 2(g - 1)`. If `A` has dimension `2m` with `m ≤ g - 1`, the
complement `A'` has dimension `2(g - 1 - m)`, and `dim A + dim A' = dim B`. -/
theorem transfer_dimensions (g gC m : Nat) (hg : 2 ≤ g) (hm : m ≤ g - 1)
    (rh : 2 * gC + 4 = 6 * g) :
    gC - g = 2 * (g - 1) ∧ 2 * m + 2 * (g - 1 - m) = gC - g := by
  omega

/-- Theorem 8.2, Weil type. The eigenspaces of `σ` on `H^{1,0}(B)` both have
dimension `g - 1`, and on `H^{1,0}(A)` both have dimension `m`. Since
`H^{1,0}(B) = H^{1,0}(A) ⊕ H^{1,0}(A')` compatibly with `σ`, the eigenspaces
on `H^{1,0}(A')` have dimensions `e₁ = e₂ = g - 1 - m`. -/
theorem complement_weil_type (g m e₁ e₂ : Nat)
    (h₁ : g - 1 = m + e₁) (h₂ : g - 1 = m + e₂) :
    e₁ = g - 1 - m ∧ e₂ = g - 1 - m ∧ e₁ = e₂ := by
  omega

/-- Theorem 8.2, the surjection. In `O_K` we have `1 + ζ + ζ^2 = 0`, so
`α ∘ (1 + σ + σ^2) = 0` and `α ∘ P = 3α` for `P = 3 - (1 + σ + σ^2)`. -/
theorem alpha_prym :
    Zz.add (Zz.add one zeta) (pow zeta 2) = zero ∧
    Zz.sub three (Zz.add (Zz.add one zeta) (pow zeta 2)) = three := by
  decide

/-- Lemma 8.1. On `A₂` of dimension `2m₂`, `V_χ` has dimension `2m₂`, so
`ω₂ ∪ ω₂`, which would lie in `∧^{4m₂} V_χ`, is zero, while `ω₂ ∪ ω̄₂` lies in
`∧^{2m₂} V_χ ⊗ ∧^{2m₂} V_χ̄`, the top degree `4m₂` of `A₂`. The class
`x ∪ pr₂^*γ` has degree `(2m₁ + 2m₂) + 2m₂`, and pushing forward along the
fibre `A₂`, of real dimension `4m₂`, lowers it to `2m₁`, the degree of the
Weil plane of `A₁`. -/
theorem twothree_degrees (m₁ m₂ : Nat) (h : 1 ≤ m₂) :
    ¬ (4 * m₂ ≤ 2 * m₂) ∧ 2 * m₂ + 2 * m₂ = 4 * m₂ ∧
    (2 * m₁ + 2 * m₂) + 2 * m₂ - 4 * m₂ = 2 * m₁ := by
  omega

/-- Remark 8.4. The varieties of Corollary 8.3 have at most `3j` moduli in
dimension `2j`: Prym varieties of etale triple covers have `3j`, abelian
surfaces of Weil type `1 ≤ 3`, Weil fourfolds `4 ≤ 6`, and `E^k × Ē^k` none.
So a product of them of total dimension `2k` has at most `3k`. -/
theorem block_moduli (j₁ j₂ f₁ f₂ : Nat) (h₁ : f₁ ≤ 3 * j₁) (h₂ : f₂ ≤ 3 * j₂) :
    1 * 1 ≤ 3 * 1 ∧ 2 * 2 ≤ 3 * 2 ∧ f₁ + f₂ ≤ 3 * (j₁ + j₂) := by
  omega

/-- `(m + k)^2 = m^2 + 2mk + k^2`. -/
theorem square_expand (m k : Nat) :
    (m + k) * (m + k) = m * m + 2 * (m * k) + k * k := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm k m]
  omega

/-- Remark 8.4. Once `m ≥ 4`, a complement of dimension `2k` with `f ≤ 3k`
moduli never gives `3(m + k) + f ≥ (m + k)^2`, for any `k`. -/
theorem count_fails (m k f : Nat) (hm : 4 ≤ m) (hf : f ≤ 3 * k) :
    3 * (m + k) + f < (m + k) * (m + k) := by
  have h₁ : 4 * m ≤ m * m := Nat.mul_le_mul_right m hm
  have h₂ : 4 * k ≤ m * k := Nat.mul_le_mul_right k hm
  have h₃ := square_expand m k
  omega

/-- Remark 8.4. At `m = 3` only `k = 0`, the Prym locus itself, passes. -/
theorem count_three (k f : Nat) (hf : f ≤ 3 * k) :
    (3 + k) * (3 + k) ≤ 3 * (3 + k) + f ↔ k = 0 := by
  have h₁ := square_expand 3 k
  have h₂ := Nat.le_mul_self k
  constructor
  · intro h
    omega
  · intro h
    subst h
    omega

/-- Remark 8.4. At `m = 2`, with the largest number `3k` of moduli, exactly
`k ≤ 2` pass. -/
theorem count_two (k : Nat) :
    (2 + k) * (2 + k) ≤ 3 * (2 + k) + 3 * k ↔ k ≤ 2 := by
  have h₁ := square_expand 2 k
  constructor
  · intro h
    apply Classical.byContradiction
    intro hk
    have h3 : 3 ≤ k := by omega
    have := Nat.mul_le_mul_right k h3
    omega
  · intro h
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide

end Spread

end FullAttempt

/-! ## Section 6. Axioms

Each line below prints the axioms a theorem depends on. None should list
`sorryAx` or `Lean.ofReduceBool`. -/

#print axioms FullAttempt.descent
#print axioms FullAttempt.middle_degree
#print axioms FullAttempt.hard_lefschetz_step
#print axioms FullAttempt.prym_locus_proper
#print axioms FullAttempt.jacobian_locus_proper
#print axioms FullAttempt.step3_isotypic
#print axioms FullAttempt.eigen_pairing_vanishes
#print axioms FullAttempt.step5_weights
#print axioms FullAttempt.step5_w_nonzero
#print axioms FullAttempt.step5_c_positive
#print axioms FullAttempt.transfer_dimensions
#print axioms FullAttempt.alpha_prym
#print axioms FullAttempt.count_fails
#print axioms FullAttempt.count_three
#print axioms FullAttempt.count_two
