# checks.jl
#
# Exact checks of the finite computations behind Section 5 of
# paper/full_attempt.tex. Base Julia only, no packages. This file mirrors
# ../python/checks.py check for check.
#
# No proof in the paper rests on these checks. They repeat, in exact integer
# and rational arithmetic, computations that the paper does by hand.
#
#   (1) Dimension counts: 3n against n^2, and 3g - 3 against g(g+1)/2.
#   (2) The Hodge classes of a general abelian variety of Weil type of
#       dimension 2n: the invariants of sl(2n) in the exterior algebra of
#       V + V*, degree by degree, for n = 1, ..., 4. Expected: one line in
#       every even degree except the middle one, where there are three (the
#       power of the polarization and the two Weil lines). Also the products
#       used in Step 5 of Theorem 5.2.
#   (3) Schoen's Lemma 1.2 as used in Step 1: the part of H^h(C^h) fixed by
#       G' on which delta^* acts by chi(1) is one-dimensional, for genus 3 by
#       summing over the whole group and for genus 3 and 4 by stabilizers.
#   (4) Steps 1 and 2: u_chi has h! terms, is fixed by the permutations of
#       the factors, and the integral of u_chi u_chibar over C^h is nonzero,
#       for h = 2, 4, 6; for h = 4 the projection found in (3) is a multiple
#       of u_chi.
#
# Run:  julia checks.jl

const FAILURES = String[]

function check(name::AbstractString, ok::Bool)
    println(ok ? "  ok    " : "  FAIL  ", name)
    ok || push!(FAILURES, String(name))
    return nothing
end

# ---------------------------------------------------------------------------
# Z[zeta], zeta^2 = -1 - zeta, as pairs (a, b) meaning a + b zeta
# ---------------------------------------------------------------------------

const ZZ = Tuple{Int,Int}

zmul(x::ZZ, y::ZZ) = (x[1] * y[1] - x[2] * y[2], x[1] * y[2] + x[2] * y[1] - x[2] * y[2])
zadd(x::ZZ, y::ZZ) = (x[1] + y[1], x[2] + y[2])
const ZETA_POW = ((1, 0), (0, 1), (-1, -1))
zeta(k::Integer) = ZETA_POW[mod(k, 3) + 1]

# ---------------------------------------------------------------------------
# (1) Dimension counts
# ---------------------------------------------------------------------------

function part1()
    println("(1) dimension counts")
    for n in 1:12
        proper = 3 * n < n * n
        check("n = $(lpad(n, 2)): 3n = $(lpad(3n, 3)), n^2 = $(lpad(n * n, 3)), Prym locus proper: $proper",
              proper == (n >= 4))
    end
    for g in 2:12
        mg = 3 * g - 3
        ag2 = g * (g + 1)
        proper = 2 * mg < ag2
        check("g = $(lpad(g, 2)): 3g-3 = $(lpad(mg, 3)), g(g+1)/2 = $(lpad(div(ag2, 2), 3)), Jacobian locus proper: $proper",
              proper == (g >= 4))
    end
end

# ---------------------------------------------------------------------------
# (2) Invariants of sl(2n) in the exterior algebra of V + V*
# ---------------------------------------------------------------------------

const Mono = Vector{Int}
const Ext = Dict{Mono,Int}

function sort_sign(seq::Vector{Int})
    s = copy(seq)
    sgn = 1
    for i in 1:length(s), j in (i + 1):length(s)
        if s[i] > s[j]
            sgn = -sgn
        end
    end
    return sgn, sort(s)
end

function prune(d::Dict{K,Int}) where {K}
    return Dict{K,Int}(k => v for (k, v) in d if v != 0)
end

function wedge(x::Ext, y::Ext)
    out = Ext()
    for (mx, cx) in x, (my, cy) in y
        isempty(intersect(mx, my)) || continue
        sg, m = sort_sign(vcat(mx, my))
        out[m] = get(out, m, 0) + sg * cx * cy
    end
    return prune(out)
end

# E maps a basis label to a list of (coefficient, basis label)
function act(E::Dict{Int,Vector{Tuple{Int,Int}}}, mono::Mono)
    out = Ext()
    for (pos, x) in enumerate(mono)
        for (c, y) in get(E, x, Tuple{Int,Int}[])
            if (y in mono) && y != x
                continue
            end
            new = copy(mono)
            new[pos] = y
            length(unique(new)) < length(new) && continue
            sg, m = sort_sign(new)
            out[m] = get(out, m, 0) + sg * c
        end
    end
    return prune(out)
end

function exact_rank(rows::Vector{Dict{Int,Int}}, ncols::Int)
    mat = Dict{Int,Rational{BigInt}}[]
    for r in rows
        d = Dict{Int,Rational{BigInt}}(k => Rational{BigInt}(v) for (k, v) in r if v != 0)
        isempty(d) || push!(mat, d)
    end
    rk = 0
    for col in 1:ncols
        piv = 0
        for i in (rk + 1):length(mat)
            if get(mat[i], col, 0) != 0
                piv = i
                break
            end
        end
        piv == 0 && continue
        mat[rk + 1], mat[piv] = mat[piv], mat[rk + 1]
        p = mat[rk + 1]
        for i in 1:length(mat)
            if i != rk + 1 && get(mat[i], col, 0) != 0
                f = mat[i][col] / p[col]
                r = copy(mat[i])
                for (k, v) in p
                    r[k] = get(r, k, 0) - f * v
                    if r[k] == 0
                        delete!(r, k)
                    end
                end
                mat[i] = r
            end
        end
        rk += 1
    end
    return rk
end

function combos(N::Int, p::Int)
    out = Vector{Mono}()
    cur = Int[]
    function rec(start::Int)
        if length(cur) == p
            push!(out, copy(cur))
            return
        end
        for k in start:(N - 1)
            push!(cur, k)
            rec(k + 1)
            pop!(cur)
        end
    end
    rec(0)
    return out
end

function sum_dicts(ds::Vector{Ext})
    out = Ext()
    for d in ds, (k, v) in d
        out[k] = get(out, k, 0) + v
    end
    return prune(out)
end

function ext_power(x::Ext, k::Int)
    out = Ext(Int[] => 1)
    for _ in 1:k
        out = wedge(out, x)
    end
    return out
end

function part2()
    println("(2) Hodge classes on a general Weil abelian variety of dimension 2n")
    for n in 1:4
        m = 2 * n          # dim V_chi
        N = 2 * m          # labels 0..m-1 for V_chi, m..2m-1 for the dual
        weight = mono -> begin
            w = zeros(Int, m)
            for x in mono
                if x < m
                    w[x + 1] += 1
                else
                    w[x - m + 1] -= 1
                end
            end
            w
        end
        # simple raising operators E_{i,i+1}: e_{i+1} -> e_i, f_i -> -f_{i+1}
        raising = Dict{Int,Vector{Tuple{Int,Int}}}[]
        for i in 0:(m - 2)
            push!(raising, Dict{Int,Vector{Tuple{Int,Int}}}(i + 1 => [(1, i)], m + i => [(-1, m + i + 1)]))
        end
        dims = Int[]
        for p in 0:(2 * m)
            zero_w = [mo for mo in combos(N, p) if length(unique(weight(mo))) == 1]
            rows = Dict{Tuple{Int,Mono},Dict{Int,Int}}()
            for (k, mo) in enumerate(zero_w)
                for (r, E) in enumerate(raising)
                    for (img, c) in act(E, mo)
                        row = get!(rows, (r, img), Dict{Int,Int}())
                        row[k] = c
                    end
                end
            end
            rk = exact_rank(collect(values(rows)), length(zero_w))
            push!(dims, length(zero_w) - rk)
        end
        even = [dims[2 * q + 1] for q in 0:m]
        odd_zero = all(dims[p + 1] == 0 for p in 1:2:(2 * m))
        expected = [q == n ? 3 : 1 for q in 0:m]
        check("n = $n: dim Hdg^q for q = 0..$m: $even; odd degrees: none", even == expected && odd_zero)
        # Step 5: eta = sum e_i ^ f_i, omega = e_0 ^ ... ^ e_{m-1}, omegabar likewise
        eta = Ext([i, m + i] => 1 for i in 0:(m - 1))
        etan = ext_power(eta, n)
        omega = Ext(collect(0:(m - 1)) => 1)
        omegabar = Ext(collect(m:(N - 1)) => 1)
        top = collect(0:(N - 1))
        eta_inv = all(isempty(sum_dicts([Ext(k => c * v for (k, v) in act(E, mo)) for (mo, c) in eta]))
                      for E in raising)
        check("n = $n: eta is invariant", eta_inv)
        check("n = $n: eta^n ^ omega = 0 and eta^n ^ omegabar = 0",
              isempty(wedge(etan, omega)) && isempty(wedge(etan, omegabar)))
        check("n = $n: eta ^ omega = 0", isempty(wedge(eta, omega)))
        e2n = ext_power(eta, 2 * n)
        check("n = $n: eta^(2n) = $(get(e2n, top, 0)) x orientation, nonzero",
              collect(keys(e2n)) == [top] && e2n[top] != 0)
        oo = wedge(omega, omegabar)
        check("n = $n: omega ^ omegabar = $(get(oo, top, 0)) x orientation, nonzero",
              collect(keys(oo)) == [top] && oo[top] != 0)
    end
end

# ---------------------------------------------------------------------------
# (3) and (4): H^*(C) with the action of sigma
# ---------------------------------------------------------------------------
# Basis labels: ('1',0) degree 0; ('a',i) degree 1, sigma-invariant (i < 2g);
# ('b',j) degree 1, sigma^* = zeta; ('c',j) degree 1, sigma^* = zeta^2
# (j < h); ('p',0) degree 2.

const Label = Tuple{Char,Int}
const Tens = Vector{Label}
const TensDict = Dict{Tens,ZZ}

function deg(x::Label)
    x[1] == '1' && return 0
    x[1] == 'p' && return 2
    return 1
end

function chr(x::Label)
    x[1] == 'b' && return 1
    x[1] == 'c' && return 2
    return 0
end

# s . (x_1 ... x_h) = eps (x_{s^-1(1)} ... x_{s^-1(h)}); s is a permutation of 1:h
function koszul_perm(tup::Tens, s::Vector{Int})
    h = length(tup)
    new = Vector{Label}(undef, h)
    for i in 1:h
        new[s[i]] = tup[i]
    end
    inv = 0
    for i in 1:h, j in (i + 1):h
        if s[i] > s[j] && isodd(deg(tup[i])) && isodd(deg(tup[j]))
            inv += 1
        end
    end
    return (iseven(inv) ? 1 : -1), new
end

function allperms(h::Int)
    out = Vector{Vector{Int}}()
    function rec(cur::Vector{Int}, rest::Vector{Int})
        if isempty(rest)
            push!(out, copy(cur))
            return
        end
        for idx in 1:length(rest)
            push!(cur, rest[idx])
            rec(cur, vcat(rest[1:(idx - 1)], rest[(idx + 1):end]))
            pop!(cur)
        end
    end
    rec(Int[], collect(1:h))
    return out
end

function basis(g::Int)
    h = 2 * g - 2
    return vcat(Label[('1', 0)], Label[('a', i) for i in 0:(2g - 1)], Label[('b', j) for j in 0:(h - 1)],
                Label[('c', j) for j in 0:(h - 1)], Label[('p', 0)])
end

# multisets of size h of B with total degree h, as sorted index vectors
function multisets(B::Vector{Label}, h::Int)
    out = Vector{Vector{Int}}()
    cur = Int[]
    function rec(start::Int, left::Int, d::Int)
        if left == 0
            d == h && push!(out, copy(cur))
            return
        end
        for k in start:length(B)
            dd = d + deg(B[k])
            dd > h && continue
            push!(cur, k)
            rec(k, left - 1, dd)
            pop!(cur)
        end
    end
    rec(1, h, 0)
    return out
end

function zprune(d::TensDict)
    return TensDict(k => v for (k, v) in d if v != (0, 0))
end

# sum over the whole group (Z/3)^h x| S_h of conj(theta(g)) g.tup, theta = zeta^(sum v)
function project_full(tup::Tens, h::Int)
    out = TensDict()
    perms = allperms(h)
    for v in Iterators.product(ntuple(_ -> 0:2, h)...)
        e = sum(v[i] * chr(tup[i]) for i in 1:h) - sum(v)
        z = zeta(e)
        for s in perms
            eps, new = koszul_perm(tup, s)
            out[new] = zadd(get(out, new, (0, 0)), (eps * z[1], eps * z[2]))
        end
    end
    return zprune(out)
end

# coefficient of tup in its own projection: sum over the stabilizer of the line
function stabilizer_coefficient(tup::Tens, h::Int)
    vsum = (1, 0)
    for x in tup
        t = (0, 0)
        for vi in 0:2
            t = zadd(t, zeta(vi * (chr(x) - 1)))
        end
        vsum = zmul(vsum, t)
    end
    vsum == (0, 0) && return (0, 0)
    blocks = Dict{Label,Int}()
    for x in tup
        blocks[x] = get(blocks, x, 0) + 1
    end
    for (x, cnt) in blocks
        if cnt > 1 && isodd(deg(x))
            return (0, 0)   # a transposition of two equal odd factors acts by -1
        end
    end
    ssum = 1
    for (x, cnt) in blocks
        ssum *= factorial(cnt)
    end
    return (vsum[1] * ssum, vsum[2] * ssum)
end

function part3()
    println("(3) Schoen's Lemma 1.2: the chi-part U_chi of H^h(C^h)^{G'}")
    g, h = 3, 4
    B = basis(g)
    dim = 0
    witness = nothing
    for ms in multisets(B, h)
        tup = Label[B[k] for k in ms]
        P = project_full(tup, h)
        if !isempty(P)
            dim += 1
            witness = (tup, P)
        end
    end
    check("g = 3, h = 4, whole-group sum: dim U_chi = $dim", dim == 1)
    for g in (3, 4)
        h = 2 * g - 2
        B = basis(g)
        dim = count(ms -> stabilizer_coefficient(Label[B[k] for k in ms], h) != (0, 0), multisets(B, h))
        check("g = $g, h = $h, stabilizers: dim U_chi = $dim", dim == 1)
    end
    return witness
end

# product in H^*(C): b_j c_k = delta p, c_k b_j = -delta p, others zero unless a unit
function cmul_factor(x::Label, y::Label)
    x[1] == '1' && return 1, y
    y[1] == '1' && return 1, x
    if x[1] == 'b' && y[1] == 'c' && x[2] == y[2]
        return 1, ('p', 0)
    end
    if x[1] == 'c' && y[1] == 'b' && x[2] == y[2]
        return -1, ('p', 0)
    end
    return 0, ('0', 0)
end

# product in H^*(C)^{tensor h} with Koszul signs; coefficients in Z[zeta]
function tmul(X::TensDict, Y::TensDict)
    out = TensDict()
    for (tx, cx) in X, (ty, cy) in Y
        h = length(tx)
        sgn = 1
        for i in 1:h, j in 1:(i - 1)
            if isodd(deg(tx[i])) && isodd(deg(ty[j]))
                sgn = -sgn
            end
        end
        new = Vector{Label}(undef, h)
        alive = true
        for i in 1:h
            c, z = cmul_factor(tx[i], ty[i])
            if c == 0
                alive = false
                break
            end
            sgn *= c
            new[i] = z
        end
        alive || continue
        c = zmul(cx, cy)
        out[new] = zadd(get(out, new, (0, 0)), (sgn * c[1], sgn * c[2]))
    end
    return zprune(out)
end

function u_class(letter::Char, h::Int)
    u = TensDict(fill(('1', 0), h) => (1, 0))
    for j in 0:(h - 1)
        s = TensDict()
        for i in 1:h
            t = fill(('1', 0), h)
            t[i] = (letter, j)
            s[t] = (1, 0)
        end
        u = tmul(u, s)
    end
    return u
end

function part4(witness)
    println("(4) Steps 1 and 2: u_chi and the pairing with u_chibar")
    for h in (2, 4, 6)
        u = u_class('b', h)
        ub = u_class('c', h)
        coeffs = Set(values(u))
        check("h = $h: u_chi has $(length(u)) terms = $(h)!, coefficients +-1",
              length(u) == factorial(h) && issubset(coeffs, Set([(1, 0), (-1, 0)])))
        # the adjacent transpositions generate the permutations
        sym = true
        for i in 1:(h - 1)
            s = collect(1:h)
            s[i], s[i + 1] = s[i + 1], s[i]
            img = TensDict()
            for (tup, c) in u
                eps, new = koszul_perm(tup, s)
                img[new] = (eps * c[1], eps * c[2])
            end
            sym = sym && img == u
        end
        check("h = $h: u_chi is fixed by the permutations of the factors", sym)
        prod_ = tmul(u, ub)
        top = fill(('p', 0), h)
        val = get(prod_, top, (0, 0))
        check("h = $h: integral of u_chi u_chibar over C^h = $(val[1]), nonzero",
              issubset(keys(prod_), Set([top])) && val != (0, 0) && val[2] == 0)
    end
    tup, P = witness
    u = u_class('b', 4)
    ratio = nothing
    prop = Set(keys(P)) == Set(keys(u))
    if prop
        k0 = first(keys(u))
        r = u[k0] == (1, 0) ? P[k0] : (-P[k0][1], -P[k0][2])
        for k in keys(u)
            ex = u[k] == (1, 0) ? r : (-r[1], -r[2])
            if P[k] != ex
                prop = false
                break
            end
        end
        ratio = r
    end
    name = join([string(x[1], x[2]) for x in tup], ".")
    check("h = 4: the projection of $name is $ratio x u_chi", prop)
end

function main()
    part1()
    part2()
    w = part3()
    part4(w)
    println()
    if !isempty(FAILURES)
        println("$(length(FAILURES)) check(s) failed")
        exit(1)
    end
    println("all checks passed")
end

main()
