"""Exact checks of the finite computations behind Section 5 of
paper/full_attempt.tex, items (1) to (4), and behind Theorem 9 of the
research note paper/weil_closure_attempt.tex, items (5) and (6). This file
mirrors ../julia/checks.jl check for check and prints the same results.

No proof in either paper rests on these checks. They repeat, in exact
integer arithmetic, computations that the papers do by hand.

  (1) Dimension counts: 3n against n^2, and 3g - 3 against g(g+1)/2.
  (2) The Hodge classes of a general abelian variety of Weil type of
      dimension 2n: the invariants of sl(2n) in the exterior algebra of
      V + V*, degree by degree, for n = 1, ..., 4. Expected: one line in
      every degree except the middle one, where there are three (the power
      of the polarization and the two Weil lines). Also the products used in
      Step 5 of Theorem 5.2.
  (3) Schoen's Lemma 1.2 as used in Step 1: the part of H^h(C^h) fixed by
      G' on which delta^* acts by chi(1) is one-dimensional, for genus 3
      by summing over the whole group and for genus 4 by stabilizers.
  (4) Steps 1 and 2: u_chi has h! terms, is fixed by the permutations, and
      the integral of u_chi u_chibar over C^h is nonzero, for h = 2, 4, 6;
      for h = 4 the projection of b_1 ... b_4 found in (3) is a multiple of
      u_chi.
  (5) Theorem 9 of the note, Step 1: the endomorphisms of V^m + V*^m that
      commute with sl(2n) form M_m(K), of dimension 2m^2, once 2n >= 3 (for
      2n = 2 the standard representation is self-dual and they form M_2m).
  (6) Theorem 9 of the note, Step 3: the sl(2n)-invariants in degree 2 on
      A^m all have type (1,1) once 2n >= 3, and there are m^2 of them, the
      rank of the Neron-Severi group of A^m; for 2n = 2 there are invariants
      of type (2,0) and (0,2) as well.

Run:  python3 checks.py
"""

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial
import sys

# ----------------------------------------------------------------------------
# Z[zeta], zeta^2 = -1 - zeta, as pairs (a, b) meaning a + b zeta
# ----------------------------------------------------------------------------

def zmul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)

def zadd(x, y):
    return (x[0] + y[0], x[1] + y[1])

ZETA_POW = [(1, 0), (0, 1), (-1, -1)]  # zeta^0, zeta^1, zeta^2

def zeta(k):
    return ZETA_POW[k % 3]

FAILURES = []

def check(name, ok):
    print(("  ok    " if ok else "  FAIL  ") + name)
    if not ok:
        FAILURES.append(name)

# ----------------------------------------------------------------------------
# (1) Dimension counts
# ----------------------------------------------------------------------------

def part1():
    print("(1) dimension counts")
    for n in range(1, 13):
        proper = 3 * n < n * n
        check(f"n = {n:2d}: 3n = {3*n:3d}, n^2 = {n*n:3d}, Prym locus proper: {proper}",
              proper == (n >= 4))
    for g in range(2, 13):
        mg, ag2 = 3 * g - 3, g * (g + 1)
        proper = 2 * mg < ag2
        check(f"g = {g:2d}: 3g-3 = {mg:3d}, g(g+1)/2 = {ag2//2:3d}, Jacobian locus proper: {proper}",
              proper == (g >= 4))

# ----------------------------------------------------------------------------
# (2) Invariants of sl(2n) in the exterior algebra of V + V*
# ----------------------------------------------------------------------------

def sort_sign(seq):
    """Sign of the permutation sorting seq (distinct entries), and the sorted tuple."""
    s = list(seq)
    sign = 1
    for i in range(len(s)):
        for j in range(i + 1, len(s)):
            if s[i] > s[j]:
                sign = -sign
    return sign, tuple(sorted(s))

def wedge(x, y):
    """Product in the exterior algebra; x, y are dicts {sorted tuple: coefficient}."""
    out = {}
    for mx, cx in x.items():
        for my, cy in y.items():
            if set(mx) & set(my):
                continue
            sg, m = sort_sign(mx + my)
            out[m] = out.get(m, 0) + sg * cx * cy
    return {m: c for m, c in out.items() if c != 0}

def act(E, mono):
    """Apply the derivation induced by E (dict basis -> list of (coeff, basis)) to a monomial."""
    out = {}
    for pos, x in enumerate(mono):
        for c, y in E.get(x, []):
            if y in mono and y != x:
                continue
            new = list(mono)
            new[pos] = y
            if len(set(new)) < len(new):
                continue
            sg, m = sort_sign(new)
            out[m] = out.get(m, 0) + sg * c
    return {m: c for m, c in out.items() if c != 0}

def rank(rows, ncols):
    """Exact rank over Q of a list of rows (dicts col -> int)."""
    mat = [{k: Fraction(v) for k, v in r.items() if v != 0} for r in rows]
    mat = [r for r in mat if r]
    rk = 0
    for col in range(ncols):
        piv = None
        for i in range(rk, len(mat)):
            if mat[i].get(col, 0) != 0:
                piv = i
                break
        if piv is None:
            continue
        mat[rk], mat[piv] = mat[piv], mat[rk]
        p = mat[rk]
        for i in range(len(mat)):
            if i != rk and mat[i].get(col, 0) != 0:
                f = mat[i][col] / p[col]
                r = dict(mat[i])
                for k, v in p.items():
                    r[k] = r.get(k, 0) - f * v
                    if r[k] == 0:
                        del r[k]
                mat[i] = r
        rk += 1
    return rk

def part2():
    print("(2) Hodge classes on a general Weil abelian variety of dimension 2n")
    for n in range(1, 5):
        m = 2 * n          # dim V_chi
        N = 2 * m          # basis e_0..e_{m-1} of V_chi, f_0..f_{m-1} of the dual
        def weight(mono):
            w = [0] * m
            for x in mono:
                if x < m:
                    w[x] += 1
                else:
                    w[x - m] -= 1
            return w
        # simple raising operators E_{i,i+1}: e_{i+1} -> e_i, f_i -> -f_{i+1}
        raising = []
        for i in range(m - 1):
            raising.append({i + 1: [(1, i)], m + i: [(-1, m + i + 1)]})
        dims = []
        for p in range(0, 2 * m + 1):
            monos = [c for c in combinations(range(N), p)]
            zero = [mo for mo in monos if len(set(weight(mo))) == 1]
            # invariants = weight-zero vectors killed by every simple raising operator
            rows = {}
            for k, mo in enumerate(zero):
                for r, E in enumerate(raising):
                    for img, c in act(E, mo).items():
                        rows.setdefault((r, img), {})[k] = c
            rk = rank(list(rows.values()), len(zero))
            dims.append(len(zero) - rk)
        even = [dims[2 * q] for q in range(0, m + 1)]
        odd_zero = all(dims[p] == 0 for p in range(1, 2 * m + 1, 2))
        expected = [3 if q == n else 1 for q in range(0, m + 1)]
        check(f"n = {n}: dim Hdg^q for q = 0..{m}: {even}; odd degrees: none", even == expected and odd_zero)
        # Step 5: eta = sum e_i ^ f_i, omega = e_0 ^ ... ^ e_{m-1}, omegabar likewise
        eta = {}
        for i in range(m):
            eta[(i, m + i)] = 1
        def power(x, k):
            out = {(): 1}
            for _ in range(k):
                out = wedge(out, x)
            return out
        etan = power(eta, n)
        omega = {tuple(range(m)): 1}
        omegabar = {tuple(range(m, N)): 1}
        top = tuple(range(N))
        eta_inv = all(sum_dicts([{k: c * v for k, v in act(E, mo).items()} for mo, c in eta.items()]) == {}
                      for E in raising)
        check(f"n = {n}: eta is invariant", eta_inv)
        check(f"n = {n}: eta^n ^ omega = 0 and eta^n ^ omegabar = 0",
              wedge(etan, omega) == {} and wedge(etan, omegabar) == {})
        check(f"n = {n}: eta ^ omega = 0", wedge(eta, omega) == {})
        e2n = power(eta, 2 * n)
        check(f"n = {n}: eta^(2n) = {e2n.get(top, 0)} x orientation, nonzero",
              set(e2n) == {top} and e2n[top] != 0)
        oo = wedge(omega, omegabar)
        check(f"n = {n}: omega ^ omegabar = {oo.get(top, 0)} x orientation, nonzero",
              set(oo) == {top} and oo[top] != 0)

def sum_dicts(ds):
    out = {}
    for d in ds:
        for k, v in d.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}

# ----------------------------------------------------------------------------
# (3) and (4): H^*(C) with the action of sigma
# ----------------------------------------------------------------------------
# Basis labels: ('1',0) degree 0; ('a',i) degree 1, sigma-invariant (i < 2g);
# ('b',j) degree 1, sigma^* = zeta; ('c',j) degree 1, sigma^* = zeta^2 (j < h);
# ('p',0) degree 2.

def deg(x):
    return {'1': 0, 'a': 1, 'b': 1, 'c': 1, 'p': 2}[x[0]]

def char(x):
    return {'1': 0, 'a': 0, 'b': 1, 'c': 2, 'p': 0}[x[0]]

def koszul_perm(tup, s):
    """s . (x_1 ... x_h) = eps (x_{s^-1(1)} ... x_{s^-1(h)}); returns (eps, new tuple)."""
    h = len(tup)
    new = [None] * h
    for i in range(h):
        new[s[i]] = tup[i]
    inv = 0
    for i in range(h):
        for j in range(i + 1, h):
            if s[i] > s[j] and deg(tup[i]) % 2 == 1 and deg(tup[j]) % 2 == 1:
                inv += 1
    return (-1) ** inv, tuple(new)

def basis(g):
    h = 2 * g - 2
    return ([('1', 0)] + [('a', i) for i in range(2 * g)] + [('b', j) for j in range(h)]
            + [('c', j) for j in range(h)] + [('p', 0)])

def multisets(B, h):
    """Multisets of size h of B with total degree h, as sorted tuples of indices."""
    out = []
    def rec(start, left, d, cur):
        if left == 0:
            if d == h:
                out.append(tuple(cur))
            return
        for k in range(start, len(B)):
            dd = d + deg(B[k])
            if dd + 0 > h:
                continue
            cur.append(k)
            rec(k, left - 1, dd, cur)
            cur.pop()
    rec(0, h, 0, [])
    return out

def project_full(tup, h):
    """Sum over the whole group H = (Z/3)^h x| S_h of conj(theta(g)) g.tup, theta = zeta^(sum v)."""
    out = {}
    perms = list(permutations(range(h)))
    for v in product(range(3), repeat=h):
        e = sum(vi * char(x) for vi, x in zip(v, tup)) - sum(v)  # times conj(theta) = zeta^(-sum v)
        z = zeta(e)
        for s in perms:
            eps, new = koszul_perm(tup, s)
            cur = out.get(new, (0, 0))
            out[new] = zadd(cur, (eps * z[0], eps * z[1]))
    return {k: c for k, c in out.items() if c != (0, 0)}

def stabilizer_coefficient(tup, h):
    """Coefficient of tup in its own projection: sum over the stabilizer of the line."""
    # v-sum: sum_v zeta^(sum v_i (psi_i - 1)) = prod_i sum_{v_i} zeta^(v_i (psi_i - 1))
    vsum = (1, 0)
    for x in tup:
        t = (0, 0)
        for vi in range(3):
            t = zadd(t, zeta(vi * (char(x) - 1)))
        vsum = zmul(vsum, t)
    if vsum == (0, 0):
        return (0, 0)
    # permutations fixing the tuple
    ssum = 0
    blocks = {}
    for i, x in enumerate(tup):
        blocks.setdefault(x, []).append(i)
    for x, pos in blocks.items():
        if len(pos) > 1 and deg(x) % 2 == 1:
            return (0, 0)  # a transposition of two equal odd factors acts by -1
    ssum = 1
    for x, pos in blocks.items():
        ssum *= factorial(len(pos))
    return (vsum[0] * ssum, vsum[1] * ssum)

def part3():
    print("(3) Schoen's Lemma 1.2: the chi-part U_chi of H^h(C^h)^{G'}")
    # genus 3, h = 4: sum over the whole group, 3^4 * 4! = 1944 elements
    g, h = 3, 4
    B = basis(g)
    dim = 0
    witness = None
    for ms in multisets(B, h):
        tup = tuple(B[k] for k in ms)
        P = project_full(tup, h)
        if P:
            dim += 1
            witness = (tup, P)
    check(f"g = 3, h = 4, whole-group sum: dim U_chi = {dim}", dim == 1)
    # genus 4, h = 6: stabilizer of each line
    for g in (3, 4):
        h = 2 * g - 2
        B = basis(g)
        dim = sum(1 for ms in multisets(B, h)
                  if stabilizer_coefficient(tuple(B[k] for k in ms), h) != (0, 0))
        check(f"g = {g}, h = {h}, stabilizers: dim U_chi = {dim}", dim == 1)
    return witness

def pullback_factor(i, x, h):
    t = [('1', 0)] * h
    t[i] = x
    return {tuple(t): (1, 0)}

def cmul_factor(x, y):
    """Product in H^*(C): b_j c_k = delta p, c_k b_j = -delta p, others zero unless a unit."""
    if x[0] == '1':
        return 1, y
    if y[0] == '1':
        return 1, x
    if x[0] == 'b' and y[0] == 'c' and x[1] == y[1]:
        return 1, ('p', 0)
    if x[0] == 'c' and y[0] == 'b' and x[1] == y[1]:
        return -1, ('p', 0)
    return 0, None

def tmul(X, Y):
    """Product in H^*(C)^{tensor h} with Koszul signs; coefficients in Z[zeta]."""
    out = {}
    for tx, cx in X.items():
        for ty, cy in Y.items():
            sign = 1
            # moving y_j past x_i for i > j
            for i in range(len(tx)):
                for j in range(i):
                    if deg(tx[i]) % 2 == 1 and deg(ty[j]) % 2 == 1:
                        sign = -sign
            new = []
            for x, y in zip(tx, ty):
                c, z = cmul_factor(x, y)
                if c == 0:
                    break
                sign *= c
                new.append(z)
            else:
                new = tuple(new)
                c = zmul(cx, cy)
                cur = out.get(new, (0, 0))
                out[new] = zadd(cur, (sign * c[0], sign * c[1]))
    return {k: c for k, c in out.items() if c != (0, 0)}

def u_class(letter, h):
    u = {tuple([('1', 0)] * h): (1, 0)}
    for j in range(h):
        s = {}
        for i in range(h):
            for k, c in pullback_factor(i, (letter, j), h).items():
                s[k] = c
        u = tmul(u, s)
    return u

def part4(witness):
    print("(4) Steps 1 and 2: u_chi and the pairing with u_chibar")
    for h in (2, 4, 6):
        u = u_class('b', h)
        ub = u_class('c', h)
        coeffs = set(u.values())
        check(f"h = {h}: u_chi has {len(u)} terms = {h}!, coefficients +-1",
              len(u) == factorial(h) and coeffs <= {(1, 0), (-1, 0)})
        # the adjacent transpositions generate the permutations
        sym = True
        for i in range(h - 1):
            s = list(range(h))
            s[i], s[i + 1] = s[i + 1], s[i]
            img = {}
            for tup, c in u.items():
                eps, new = koszul_perm(tup, tuple(s))
                img[new] = (eps * c[0], eps * c[1])
            sym = sym and img == u
        check(f"h = {h}: u_chi is fixed by the permutations of the factors", sym)
        prod_ = tmul(u, ub)
        top = tuple([('p', 0)] * h)
        val = prod_.get(top, (0, 0))
        check(f"h = {h}: integral of u_chi u_chibar over C^h = {val[0]}, nonzero",
              set(prod_) <= {top} and val != (0, 0) and val[1] == 0)
    # the witness of (3), h = 4, is a multiple of u_chi
    tup, P = witness
    u = u_class('b', 4)
    ratio = None
    prop = set(P) == set(u)
    if prop:
        k0 = next(iter(u))
        # P[k] = r u[k] with r in Z[zeta]; u[k] = +-1
        r = P[k0] if u[k0] == (1, 0) else (-P[k0][0], -P[k0][1])
        for k in u:
            exp = r if u[k] == (1, 0) else (-r[0], -r[1])
            if P[k] != exp:
                prop = False
                break
        ratio = r
    check(f"h = 4: the projection of {'.'.join(x[0] + str(x[1]) for x in tup)} is {ratio} x u_chi", prop)


# ----------------------------------------------------------------------------
# (5) and (6): the research note, Theorem 9 (the barrier)
# ----------------------------------------------------------------------------
# sl(2n) acts diagonally on m copies of V + V*. Labels: e_{c,i} = c*2n + i and
# f_{c,i} = 2nm + c*2n + i, for copies c < m and indices i < 2n.

def generators(n, m):
    """The Chevalley generators E_{i,i+1} and E_{i+1,i} of sl(2n), acting on labels."""
    k = 2 * n
    gens = []
    for i in range(k - 1):
        for a, b in ((i, i + 1), (i + 1, i)):
            E = {}
            for c in range(m):
                # E_{ab}: e_b -> e_a, f_a -> -f_b
                E[c * k + b] = [(1, c * k + a)]
                E[k * m + c * k + a] = [(-1, k * m + c * k + b)]
            gens.append(E)
    return gens

def commutant_dimension(n, m):
    """dim of the endomorphisms of V^m + V*^m commuting with sl(2n)."""
    N = 4 * n * m
    rows = []
    for E in generators(n, m):
        M = {}
        for src, imgs in E.items():
            for c, tgt in imgs:
                M[(tgt, src)] = c
        # (M X - X M)[r][q] = sum_k M[r][k] X[k][q] - X[r][k] M[k][q]
        eqs = {}
        for (r, k), c in M.items():
            for q in range(N):
                eqs.setdefault((r, q), {})
                eqs[(r, q)][k * N + q] = eqs[(r, q)].get(k * N + q, 0) + c
        for (k, q), c in M.items():
            for r in range(N):
                eqs.setdefault((r, q), {})
                eqs[(r, q)][r * N + k] = eqs[(r, q)].get(r * N + k, 0) - c
        rows.extend(eqs.values())
    return N * N - rank(rows, N * N)

def invariants_degree2(n, m, kind):
    """dim of the sl(2n)-invariants in the part of the exterior square of
    V^m + V*^m spanned by e^e ('VV'), f^f ('WW') or e^f ('VW')."""
    k = 2 * n
    V = list(range(k * m))
    W = list(range(k * m, 2 * k * m))
    if kind == 'VV':
        monos = list(combinations(V, 2))
    elif kind == 'WW':
        monos = list(combinations(W, 2))
    else:
        monos = [(x, y) for x in V for y in W]
    rows = {}
    for r, E in enumerate(generators(n, m)):
        for j, mo in enumerate(monos):
            for img, c in act(E, mo).items():
                rows.setdefault((r, img), {})[j] = c
    return len(monos) - rank(list(rows.values()), len(monos))

def part5():
    print("(5) Theorem 9 of the note, Step 1: the commutant of SU(V,H) on H^1(A^m)")
    for n in (1, 2, 3):
        for m in (1, 2):
            d = commutant_dimension(n, m)
            exp = 4 * m * m if n == 1 else 2 * m * m
            check(f"n = {n}, m = {m}: commuting endomorphisms span {d} dimensions, "
                  f"expected {exp} ({'M_2m' if n == 1 else 'M_m(K)'})", d == exp)

def part6():
    print("(6) Theorem 9 of the note, Step 3: invariants in degree 2 on A^m")
    for n in (1, 2, 3):
        for m in (1, 2, 3):
            vv = invariants_degree2(n, m, 'VV')
            ww = invariants_degree2(n, m, 'WW')
            vw = invariants_degree2(n, m, 'VW')
            if n == 1:
                ok = vv == ww == m * (m + 1) // 2 and vw == m * m
            else:
                ok = vv == 0 and ww == 0 and vw == m * m
            check(f"n = {n}, m = {m}: invariants of type (2,0): {vv}, (0,2): {ww}, (1,1): {vw}", ok)

if __name__ == "__main__":
    part1()
    part2()
    w = part3()
    part4(w)
    part5()
    part6()
    print()
    if FAILURES:
        print(f"{len(FAILURES)} check(s) failed")
        sys.exit(1)
    print("all checks passed")
