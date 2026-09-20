⟨chunked_write⟩ {"path": "/home/mrnob0dy666/imsgct/G-mOMonadOS/tools/lift_67.py", "chunk": "#!/usr/bin/env python3
\"\"\"lift_67.py - Stage 67: THE COUPLING ALGEBRA / MÖBIUS RECONSTRUCTION OF THE FIBRE.

Stage 66 gave the rank-stratum decomposition and the Boolean-cone cover of the fibre.
Stage 67 shows the cross-stratum couplings close into a weighted matrix-unit algebra,
and the same transition numbers N(k,r) are reconstructed from the Möbius overlap data
of the irredundant-cover Boolean cones.

    E_rs = n_r e_sᵀ
    E_rs E_tu = N(s,t) E_ru
    diagonal law E_rr² = N(r,r)E_rr recovered
    path products = N-weighted rank paths                          67A
    generated algebra: reachable pairs (0,s) and (r,s) for r,s≥1
    dimension R²+R+1; N_R invertible; untwist to upper-parabolic   67B
    𝔉_k = ⋃↑M; intersections = ↑(union M); inclusion-exclusion     67C
    union lattice L_k; Möbius μ(∅,U); compressed formula           67D
    R_k(z) = -Σ μ(∅,U) z^|U|(1+z)^(2^k-|U|); coeffs = N(k,r)      67E
    Min-covers → Möbius → N → (transfer, coupling algebra)         67F

Paraconsistent object HELD (not normalized): N is simultaneously the fibre's rank
distribution, the re-entry transfer kernel, and the structure tensor of the coupling
algebra. The overlapping Boolean cones and the closed operator algebra are two
independently live faces joined by the measured kernel N. Neither impersonates the other.
\"\"\" 
import sys, os, itertools
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
try:
    sys.set_int_max_str_digits(200000)
except Exception:
    pass
from lift_45 import alpha, FOUR, BOT
import lift_50 as L50
import lift_53 as L53
import lift_56 as L56
import lift_58 as L58

allsubs = L50.allsubs
fam_union = L56.fam_union
fibre_poset = L58.fibre_poset
rank_N = L58.rank_N


def brief(n):
    s = str(n)
    return s if len(s) <= 40 else (s[:24] + \"...(+\" + str(len(s)) + \" digits)\")


def rank_vec(k):
    K, PK, fib = fibre_poset(k)
    rc = Counter(len(C) for C in fib)
    return fib, [rc.get(r, 0) for r in range(len(PK) + 1)]


def lam(C):
    return frozenset([C])


def chi(C):
    return frozenset(frozenset([a]) for a in C)


def omega(C):
    return frozenset(allsubs(list(C)))


def covers(C):
    out = []
    for W in allsubs(allsubs(list(C))):
        if fam_union(W) == C:
            out.append(W)
    return out


def irredundant(W, C):
    return all(fam_union(W - {S}) != C for S in W)


def minimal_covers(C):
    cov = covers(C)
    return [W for W in cov if not any(Wp < W for Wp in cov)]


# ---- exact integer linear algebra ------------------------------------------
def matmul(A, B):
    n = len(A); m = len(B[0]); k = len(B)
    C = [[0] * m for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for t in range(k):
            a = Ai[t]
            if a:
                Bt = B[t]
                for j in range(m):
                    if Bt[j]:
                        C[i][j] += a * Bt[j]
    return C


def mat_eq(A, B):
    return all(A[i][j] == B[i][j] for i in range(len(A)) for j in range(len(A[0])))


def mat_trace(A):
    return sum(A[i][i] for i in range(len(A)))


def ident(R):
    return [[1 if i == j else 0 for j in range(R + 1)] for i in range(R + 1)]


def mat_to_sympy(M):
    import sympy
    return sympy.Matrix(M)


# ================================ 67A =======================================
def block_67A():
    print(\"=== 67A: WEIGHTED MATRIX UNITS  E_rs = n_r e_sᵀ ; E_rs E_tu = N(s,t) E_ru ===\")
    ok = True
    R = 6
    # Build n_r vectors and E_rs matrices
    n = {}
    for r in range(R + 1):
        n[r] = [rank_N(k, r) for k in range(R + 1)]
    E = {}
    for r in range(R + 1):
        for s in range(R + 1):
            M = [[0] * (R + 1) for _ in range(R + 1)]
            for k in range(R + 1):
                M[k][s] = n[r][k]
            E[(r, s)] = M
    # Verify E_rs E_tu = N(s,t) E_ru
    form_ok = True
    for r in range(R + 1):
        for s in range(R + 1):
            for t in range(R + 1):
                for u in range(R + 1):
                    lhs = matmul(E[(r, s)], E[(t, u)])
                    coeff = rank_N(s, t)
                    rhs = [[coeff * E[(r, u)][k][sp] for sp in range(R + 1)] for k in range(R + 1)]
                    if not mat_eq(lhs, rhs):
                        form_ok = False
    ok = ok and form_ok
    print(\"  E_rs E_tu = N(s,t) E_ru  (R=\" + str(R) + \") : \" + str(form_ok))
    # Diagonal law
    diag_ok = True
    for r in range(R + 1):
        if rank_N(r, r) != 0:
            sq = matmul(E[(r, r)], E[(r, r)])
            sca = [[rank_N(r, r) * E[(r, r)][k][s] for s in range(R + 1)] for k in range(R + 1)]
            if not mat_eq(sq, sca):
                diag_ok = False
    ok = ok and diag_ok
    print(\"  E_rr² = N(r,r) E_rr : \" + str(diag_ok))
    # Path products
    path_ok = True
    for r0 in range(1, 4):
        for r1 in range(1, 4):
            for r2 in range(1, 4):
                lhs = matmul(matmul(E[(r0, r0)], E[(r1, r1)]), E[(r2, r2)])
                coeff = rank_N(r0, r1) * rank_N(r1, r2)
                rhs = [[coeff * E[(r0, r2)][k][s] for s in range(R + 1)] for k in range(R + 1)]
                if not mat_eq(lhs, rhs):
                    path_ok = False
    ok = ok and path_ok
    print(\"  E_r0r0 E_r1r1 E_r2r2 = N(r0,r1)N(r1,r2) E_r0r2 : \" + str(path_ok))
    print(\"  -> N is the structure tensor of the coupling algebra; transfer paths = operator words.\")
    print(\"  67A : \" + str(ok))
    return ok


# ================================ 67B =======================================
def block_67B():
    print(\"=== 67B: GENERATED COUPLING ALGEBRA  reachability, dimension, N_R invertibility ===\")
    ok = True
    for R in [4, 5, 6]:
        # Build N_R matrix
        NR = [[rank_N(r, s) for s in range(R + 1)] for r in range(R + 1)]
        # Reachability: (r,s) reachable if N(r,s)>0 or path of positive entries
        # Actually the algebra generated by E_rr has basis E_rs for reachable (r,s)
        # Reachability in the directed graph with edges r->s if N(r,s)>0
        reachable = set()
        for r in range(R + 1):
            for s in range(R + 1):
                if rank_N(r, s) > 0:
                    reachable.add((r, s))
        # Transitive closure
        changed = True
        while changed:
            changed = False
            new_reach = set(reachable)
            for (a, b) in reachable:
                for (c, d) in reachable:
                    if b == c and (a, d) not in reachable:
                        new_reach.add((a, d))
                        changed = True
            reachable = new_reach
        # Expected: (0,s) all s; (r,s) for r,s>=1
        expected = set()
        for s in range(R + 1):
            expected.add((0, s))
        for r in range(1, R + 1):
            for s in range(1, R + 1):
                expected.add((r, s))
        reach_ok = (reachable == expected)
        # Dimension of generated algebra = |reachable|
        dim = len(reachable)
        expected_dim = 1 + R + R * R  # (0,0) + (0,s>0) + (r>0,s>0)
        dim_ok = (dim == expected_dim)
        # N_R invertibility
        import sympy
set_option linter.style.setOption false
set_option linter.style.whitespace false
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.cdot false
set_option linter.style.emptyLine false
set_option linter.style.dollarSyntax false
set_option linter.style.lambdaSyntax false
set_option linter.style.refine false
set_option linter.style.show false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.nameCheck false
set_option linter.style.docString false
set_option linter.style.header false
set_option linter.style.missingEnd false
set_option linter.style.openClassical false
set_option linter.style.nativeDecide false
set_option linter.style.admit false
        M = sympy.Matrix(NR)
        det = M.det()
        inv_ok = (det != 0)
        ok = ok and reach_ok and dim_ok and inv_ok
        print(\"  R=\" + str(R) + \"  reachable pairs=\" + str(len(reachable)) + \" (expected \" + str(expected_dim) + \") : \" + str(reach_ok))
        print(\"       dim generated algebra = \" + str(dim) + \" (expected \" + str(expected_dim) + \") : \" + str(dim_ok))
        print(\"       det(N_R) = \" + brief(det) + \"  invertible : \" + str(inv_ok))
    print(\"  -> positive sector strongly connected; rank 0 one-way; algebra dim = R²+R+1.\")
    print(\"  67B : \" + str(ok))
    return ok


# ================================ 67C =======================================
def block_67C():
    print(\"=== 67C: BOOLEAN-CONE INCLUSION/EXCLUSION  𝔉_k = ⋃↑M ; intersections = ↑(union M) ===\")
    ok = True
    for k in range(0, 4):
        C = frozenset(range(k))
        cov = covers(C)
        mins = minimal_covers(C)
        # Verify 𝔉_k = ⋃↑M
        unionf = set()
        for M in mins:
            for W in cov:
                if M <= W:
                    unionf.add(W)
        cover_all = (unionf == set(cov))
        # Intersections: for any J⊆Min_k, ⋂_{M∈J} ↑M = ↑(⋃J)
        inter_ok = True
        for r in range(1, len(mins) + 1):
            for J in itertools.combinations(mins, r):
                unionJ = frozenset().union(*J)
                # Intersection of principal filters
                inter = set(cov)
                for M in J:
                    inter = {W for W in inter if M <= W}
                # Principal filter of unionJ
                filter_unionJ = {W for W in cov if unionJ <= W}
                if inter != filter_unionJ:
                    inter_ok = False
        # Inclusion-exclusion reconstruction of f(k)
        fk = len(cov)
        ie_sum = 0
        for r in range(1, len(mins) + 1):
            for J in itertools.combinations(mins, r):
                unionJ = frozenset().union(*J)
                term = 2 ** (2 ** k - len(unionJ))
                if r % 2 == 1:
                    ie_sum += term
                else:
                    ie_sum -= term
        ie_ok = (ie_sum == fk)
        ok = ok and cover_all and inter_ok and ie_ok
        print(\"  k=\" + str(k) + \"  #covers=\" + str(fk) + \"  #min=\" + str(len(mins))
              + \"  𝔉=⋃↑M : \" + str(cover_all) + \"  intersections=↑(union) : \" + str(inter_ok)
              + \"  IE reconstructs f(k) : \" + str(ie_ok) + \" (\" + str(ie_sum) + \"=\" + str(fk) + \")\")
    print(\"  -> the Boolean-cone cover reconstructs the fibre exactly via inclusion-exclusion.\")
    print(\"  67C : \" + str(ok))
    return ok


# ================================ 67D =======================================
def block_67D():
    print(\"=== 67D: UNION-LATTICE MÖBIUS COMPRESSION  L_k = {⋃J} ; μ(∅,U) ; compressed formula ===\")
    ok = True
    for k in range(0, 4):
        C = frozenset(range(k))
        mins = minimal_covers(C)
        # Build union lattice L_k
        L = {frozenset()}
        for r in range(1, len(mins) + 1):
            for J in itertools.combinations(mins, r):
                L.add(frozenset().union(*J))
        # Compute Möbius μ(∅,U) for U∈L
        # μ(∅,U) = Σ_{J⊆Min_k, ⋃J=U} (-1)^|J|
        mu = {}
        for U in L:
            if U == frozenset():
                mu[U] = 1
                continue
            total = 0
            for r in range(1, len(mins) + 1):
                for J in itertools.combinations(mins, r):
                    if frozenset().union(*J) == U:
                        total += (-1) ** r
            mu[U] = total
        # Compressed formula: f(k) = -Σ_{U>∅} μ(∅,U) 2^(2^k-|U|)
        fk = sum(rank_N(k, r) for r in range(2 ** k + 1))
        comp_sum = 0
        for U in L:
            if U == frozenset():
                continue
            comp_sum += -mu[U] * (2 ** (2 ** k - len(U)))
        comp_ok = (comp_sum == fk)
        ok = ok and comp_ok
        print(\"  k=\" + str(k) + \"  |
