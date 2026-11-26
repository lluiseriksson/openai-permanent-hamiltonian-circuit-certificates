"""PERM-HC-LB-CERT-1.0: Exact rational/finite-field certificate verifier for
OpenAI's 'Circuit lower bounds for Hamiltonian cycle and the permanent' (Nov 24, 2026).

Strictly zero floating-point arithmetic, zero ast.Div / /=, zero math imports.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
from typing import Any

SCHEMA_VERSION = "PERM-HC-LB-CERT-1.0"
MAX_JSON_BYTES = 1_000_000
MAX_RATIONAL_ABS = 10**12
MAX_GRAPH_N = 8
MAX_MAT_DIM = 36
MAX_LIST_LEN = 64


class VerificationError(ValueError):
    """Raised when a PERM-HC-LB-CERT-1.0 certificate fails any check."""


def _reject_json_constant(val: str) -> Any:
    raise VerificationError(f"Non-standard JSON constant forbidden: {val!r}")


def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise VerificationError(f"Duplicate JSON key: {k!r}")
        out[k] = v
    return out


def _gcd(a: int, b: int) -> int:
    a = -a if a < 0 else a
    b = -b if b < 0 else b
    while b != 0:
        a, b = b, a % b
    return a


def _is_prime(p: int) -> bool:
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True


def _req_dict(obj: Any, name: str) -> dict[str, Any]:
    if not isinstance(obj, dict):
        raise VerificationError(f"{name} must be a JSON object")
    return obj


def _req_list(obj: Any, name: str, max_len: int = MAX_LIST_LEN) -> list[Any]:
    if not isinstance(obj, list):
        raise VerificationError(f"{name} must be a JSON array")
    if len(obj) > max_len:
        raise VerificationError(f"{name} exceeds max length {max_len}")
    return obj


def _req_str(obj: Any, name: str) -> str:
    if not isinstance(obj, str) or not obj.strip():
        raise VerificationError(f"{name} must be a non-empty string")
    return obj


def _req_int(obj: Any, name: str, lo: int | None = None, hi: int | None = None) -> int:
    if isinstance(obj, bool) or not isinstance(obj, int):
        raise VerificationError(f"{name} must be an integer")
    if lo is not None and obj < lo:
        raise VerificationError(f"{name}={obj} < {lo}")
    if hi is not None and obj > hi:
        raise VerificationError(f"{name}={obj} > {hi}")
    return obj


def _req_bool(obj: Any, name: str) -> bool:
    if not isinstance(obj, bool):
        raise VerificationError(f"{name} must be a boolean")
    return obj


def _req_frac(obj: Any, name: str) -> Fraction:
    if not isinstance(obj, list) or len(obj) != 2:
        raise VerificationError(f"{name} must be a [p, q] rational pair")
    p = _req_int(obj[0], f"{name}[0]", -MAX_RATIONAL_ABS, MAX_RATIONAL_ABS)
    q = _req_int(obj[1], f"{name}[1]", 1, MAX_RATIONAL_ABS)
    if _gcd(p, q) != 1:
        raise VerificationError(f"{name}=[{p},{q}] is not in lowest terms")
    return Fraction(p, q)


def _req_frac_vec(obj: Any, name: str, expected_len: int | None = None) -> list[Fraction]:
    arr = _req_list(obj, name)
    if expected_len is not None and len(arr) != expected_len:
        raise VerificationError(f"{name} length {len(arr)} != {expected_len}")
    return [_req_frac(x, f"{name}[{i}]") for i, x in enumerate(arr)]


def _req_frac_mat(obj: Any, name: str, rows: int | None = None, cols: int | None = None) -> list[list[Fraction]]:
    arr = _req_list(obj, name, max_len=MAX_MAT_DIM)
    if len(arr) == 0:
        raise VerificationError(f"{name} must be non-empty")
    if rows is not None and len(arr) != rows:
        raise VerificationError(f"{name} row count {len(arr)} != {rows}")
    c0: int | None = cols
    mat: list[list[Fraction]] = []
    for i, r in enumerate(arr):
        rl = _req_list(r, f"{name}[{i}]", max_len=MAX_MAT_DIM)
        if len(rl) == 0:
            raise VerificationError(f"{name}[{i}] must be non-empty")
        if c0 is None:
            c0 = len(rl)
        elif len(rl) != c0:
            raise VerificationError(f"{name}[{i}] col count {len(rl)} != {c0}")
        mat.append([_req_frac(v, f"{name}[{i}][{j}]") for j, v in enumerate(rl)])
    return mat


def _req_int_mat(obj: Any, name: str, rows: int | None = None, cols: int | None = None) -> list[list[int]]:
    arr = _req_list(obj, name, max_len=MAX_MAT_DIM)
    if len(arr) == 0:
        raise VerificationError(f"{name} must be non-empty")
    if rows is not None and len(arr) != rows:
        raise VerificationError(f"{name} row count {len(arr)} != {rows}")
    c0: int | None = cols
    mat: list[list[int]] = []
    for i, r in enumerate(arr):
        rl = _req_list(r, f"{name}[{i}]", max_len=MAX_MAT_DIM)
        if len(rl) == 0:
            raise VerificationError(f"{name}[{i}] must be non-empty")
        if c0 is None:
            c0 = len(rl)
        elif len(rl) != c0:
            raise VerificationError(f"{name}[{i}] col count {len(rl)} != {c0}")
        mat.append([_req_int(v, f"{name}[{i}][{j}]", -MAX_RATIONAL_ABS, MAX_RATIONAL_ABS) for j, v in enumerate(rl)])
    return mat


def _perms_with_info(n: int) -> list[tuple[tuple[int, ...], int, bool]]:
    """Return all permutations of 0..n-1 with (perm, sign in {+1,-1}, is_single_cycle)."""
    out: list[tuple[tuple[int, ...], int, bool]] = []
    used = [False] * n
    cur: list[int] = []

    def rec() -> None:
        if len(cur) == n:
            perm = tuple(cur)
            # Compute cycle decomposition -> parity and single-cycle flag
            vis = [False] * n
            cycles = 0
            for start in range(n):
                if not vis[start]:
                    cycles += 1
                    u = start
                    while not vis[u]:
                        vis[u] = True
                        u = perm[u]
            sgn = 1 if ((n - cycles) % 2 == 0) else -1
            out.append((perm, sgn, cycles == 1))
            return
        for v in range(n):
            if not used[v]:
                used[v] = True
                cur.append(v)
                rec()
                cur.pop()
                used[v] = False

    rec()
    return out


def _per_det_hc_frac(mat: list[list[Fraction]]) -> tuple[Fraction, Fraction, Fraction]:
    n = len(mat)
    per = Fraction(0, 1)
    det = Fraction(0, 1)
    hc = Fraction(0, 1)
    for perm, sgn, is_hc in _perms_with_info(n):
        prod = Fraction(1, 1)
        for i in range(n):
            prod = prod * mat[i][perm[i]]
            if prod == 0:
                break
        if prod != 0:
            per = per + prod
            det = det + (prod if sgn == 1 else -prod)
            if is_hc:
                hc = hc + prod
    return per, det, hc


def _mat_rank_q(mat: list[list[Fraction]]) -> int:
    m, n = len(mat), len(mat[0])
    a = [list(row) for row in mat]
    rank = 0
    for col in range(n):
        piv = -1
        for r in range(rank, m):
            if a[r][col] != 0:
                piv = r
                break
        if piv == -1:
            continue
        a[rank], a[piv] = a[piv], a[rank]
        pv = a[rank][col]
        inv_pv = Fraction(pv.denominator, pv.numerator)
        for r in range(rank + 1, m):
            if a[r][col] != 0:
                fac = a[r][col] * inv_pv
                for c in range(col, n):
                    a[r][c] = a[r][c] - fac * a[rank][c]
        rank += 1
        if rank == m:
            break
    return rank


def _mat_det_fp(mat: list[list[int]], p: int) -> int:
    n = len(mat)
    a = [[v % p for v in row] for row in mat]
    det = 1
    for col in range(n):
        piv = -1
        for r in range(col, n):
            if a[r][col] != 0:
                piv = r
                break
        if piv == -1:
            return 0
        if piv != col:
            a[col], a[piv] = a[piv], a[col]
            det = (-det) % p
        pv = a[col][col]
        det = (det * pv) % p
        inv_pv = pow(pv, p - 2, p)
        for r in range(col + 1, n):
            if a[r][col] != 0:
                fac = (a[r][col] * inv_pv) % p
                for c in range(col, n):
                    a[r][c] = (a[r][c] - fac * a[col][c]) % p
    return det


def _per_det_hc_fp(mat: list[list[int]], p: int) -> tuple[int, int, int]:
    n = len(mat)
    per = 0
    det = 0
    hc = 0
    for perm, sgn, is_hc in _perms_with_info(n):
        prod = 1
        for i in range(n):
            prod = (prod * mat[i][perm[i]]) % p
            if prod == 0:
                break
        if prod != 0:
            per = (per + prod) % p
            det = (det + (prod if sgn == 1 else -prod)) % p
            if is_hc:
                hc = (hc + prod) % p
    return per, det, hc


def _reduce_frac_mat_fp(mat: list[list[Fraction]], p: int) -> list[list[int]]:
    """Validate every entry has denominator coprime to p and reduce entrywise into F_p."""
    out: list[list[int]] = []
    for i, row in enumerate(mat):
        r_out: list[int] = []
        for j, f in enumerate(row):
            if f.denominator % p == 0:
                raise VerificationError(
                    f"Matrix entry ({i},{j})={f} has denominator divisible by field_char={p} (pole in F_{p})"
                )
            r_out.append((f.numerator * pow(f.denominator, p - 2, p)) % p)
        out.append(r_out)
    return out


# ---------------------------------------------------------------------------
# Mode 1: sparse_gadgets_and_per_hc_det (Sec. 1, Lemma 3.4, Corollary 3.5)
# ---------------------------------------------------------------------------
def _verify_mode1(cert: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(cert.get("submode"), "submode")
    if submode not in ("lemma34_coupling_gadget", "sparse_per_det_hc"):
        raise VerificationError(f"Unknown Mode 1 submode: {submode!r}")

    if submode == "lemma34_coupling_gadget":
        # Verify the exact 3x3 permanent coupling matrix A over Q or odd F_p (p. 15)
        field_char = _req_int(cert.get("field_char"), "field_char", 0, 10007)
        if field_char == 2 or (field_char != 0 and not _is_prime(field_char)):
            raise VerificationError("Lemma 3.4 permanent coupling gadget requires char != 2 (0 or odd prime)")
        a_mat = _req_frac_mat(cert.get("gadget_matrix_A"), "gadget_matrix_A", rows=3, cols=3)

        if field_char == 0:
            per_full, _, _ = _per_det_hc_frac(a_mat)
            if per_full != Fraction(1, 1):
                raise VerificationError(f"per(A)={per_full} != 1")
            for dr in (0, 1):
                for dc in (0, 1):
                    sub = [[a_mat[r][c] for c in range(3) if c != dc] for r in range(3) if r != dr]
                    per_sub, _, _ = _per_det_hc_frac(sub)
                    if per_sub != Fraction(0, 1):
                        raise VerificationError(f"Deleting ({dr},{dc}) leaves permanent {per_sub} != 0")
            if a_mat[2][2] != Fraction(1, 1):
                raise VerificationError(f"A[2][2]={a_mat[2][2]} != 1")
        else:
            # Reduce EVERY entry into F_p BEFORE computing any permanent (prevents 1/p pole cancellation!)
            a_fp = _reduce_frac_mat_fp(a_mat, field_char)
            per_full_fp, _, _ = _per_det_hc_fp(a_fp, field_char)
            if per_full_fp != 1:
                raise VerificationError(f"per(A)={per_full_fp} != 1 mod {field_char}")
            for dr in (0, 1):
                for dc in (0, 1):
                    sub_fp = [[a_fp[r][c] for c in range(3) if c != dc] for r in range(3) if r != dr]
                    per_sub_fp, _, _ = _per_det_hc_fp(sub_fp, field_char)
                    if per_sub_fp != 0:
                        raise VerificationError(f"Deleting ({dr},{dc}) leaves permanent {per_sub_fp} != 0 mod {field_char}")
            if a_fp[2][2] != 1:
                raise VerificationError(f"A[2][2]={a_fp[2][2]} != 1 mod {field_char}")

        return {
            "mode": "sparse_gadgets_and_per_hc_det",
            "submode": submode,
            "field_char": field_char,
            "per_A": 1,
            "single_deleted_minors_zero": 4,
            "A_33": 1,
        }

    # submode == "sparse_per_det_hc" (Sec. 1 & Cor. 3.5 degree-<=3 graph polynomial evaluation)
    n = _req_int(cert.get("order_N"), "order_N", 2, MAX_GRAPH_N)
    max_deg = _req_int(cert.get("max_degree_bound"), "max_degree_bound", 1, n)
    field_char = _req_int(cert.get("field_char"), "field_char", 0, 10007)
    if field_char != 0 and not _is_prime(field_char):
        raise VerificationError("field_char must be 0 or prime")
    x_mat = _req_frac_mat(cert.get("matrix_X"), "matrix_X", rows=n, cols=n)

    if field_char == 0:
        nnz_total = 0
        for i in range(n):
            out_deg = sum(1 for j in range(n) if x_mat[i][j] != 0)
            in_deg = sum(1 for j in range(n) if x_mat[j][i] != 0)
            nnz_total += out_deg
            if out_deg > max_deg or in_deg > max_deg:
                raise VerificationError(f"Vertex {i} degree (in={in_deg}, out={out_deg}) exceeds {max_deg}")
        if nnz_total == 0:
            raise VerificationError("Vacuous all-zero matrix_X")
        per_v, det_v, hc_v = _per_det_hc_frac(x_mat)
    else:
        # Validate and reduce EVERY entry into F_p BEFORE degree check and polynomial evaluation!
        x_fp = _reduce_frac_mat_fp(x_mat, field_char)
        nnz_total = 0
        for i in range(n):
            out_deg = sum(1 for j in range(n) if x_fp[i][j] != 0)
            in_deg = sum(1 for j in range(n) if x_fp[j][i] != 0)
            nnz_total += out_deg
            if out_deg > max_deg or in_deg > max_deg:
                raise VerificationError(f"Vertex {i} degree (in={in_deg}, out={out_deg}) exceeds {max_deg}")
        if nnz_total == 0:
            raise VerificationError("Vacuous all-zero matrix_X over F_p")
        p_fp, d_fp, h_fp = _per_det_hc_fp(x_fp, field_char)
        per_v, det_v, hc_v = Fraction(p_fp, 1), Fraction(d_fp, 1), Fraction(h_fp, 1)
    exp_per = _req_frac(cert.get("expected_per"), "expected_per")
    exp_det = _req_frac(cert.get("expected_det"), "expected_det")
    exp_hc = _req_frac(cert.get("expected_hc"), "expected_hc")
    if per_v != exp_per or det_v != exp_det or hc_v != exp_hc:
        raise VerificationError(
            f"(Per,Det,HC)=({per_v},{det_v},{hc_v}) != expected ({exp_per},{exp_det},{exp_hc})"
        )
    if field_char == 2 and per_v != det_v:
        raise VerificationError("In char 2, Per_N must equal Det_N")
    expect_per_ne_det = _req_bool(cert.get("expect_per_ne_det"), "expect_per_ne_det")
    if expect_per_ne_det and per_v == det_v:
        raise VerificationError("Expected Per_N != Det_N outside char 2")
    if not expect_per_ne_det and per_v != det_v:
        raise VerificationError("Expected Per_N == Det_N")

    return {
        "mode": "sparse_gadgets_and_per_hc_det",
        "submode": submode,
        "order_N": n,
        "field_char": field_char,
        "Per": [per_v.numerator, per_v.denominator],
        "Det": [det_v.numerator, det_v.denominator],
        "HC": [hc_v.numerator, hc_v.denominator],
    }


# ---------------------------------------------------------------------------
# Mode 2: balanced_cut_and_poincare (Sec. 1.3, Lemma 3.3, Lemma 4.1, Thm. 4.2)
# ---------------------------------------------------------------------------
def _verify_mode2(cert: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(cert.get("submode"), "submode")
    if submode not in ("four_row_balanced_cut_rank", "poincare_and_barycentric_smoothing"):
        raise VerificationError(f"Unknown Mode 2 submode: {submode!r}")

    if submode == "four_row_balanced_cut_rank":
        # Sec. 1.3 example: T = E_{12}(q) x E_{34}(q) + E_{13}(q) x E_{24}(q) on disjoint local supports (side 2q per row)
        q = _req_int(cert.get("wire_dim_q"), "wire_dim_q", 2, 3)
        side = 2 * q  # indices 0..q-1 for term 1, q..2q-1 for term 2
        if side * side > MAX_MAT_DIM:
            raise VerificationError("Flattening dimension (2q)^2 exceeds MAX_MAT_DIM")
        dim_cut = side * side
        # Build all 3 balanced 2|2 cuts of {0,1,2,3}:
        # Cut A: {0,1} | {2,3}; Cut B: {0,2} | {1,3}; Cut C: {0,3} | {1,2}
        # Term 1: x0==x1 in [0..q-1] AND x2==x3 in [0..q-1]
        # Term 2: x0==x2 in [q..2q-1] AND x1==x3 in [q..2q-1]
        cuts = [
            ("12|34", (0, 1), (2, 3)),
            ("13|24", (0, 2), (1, 3)),
            ("14|23", (0, 3), (1, 2)),
        ]
        ranks_t1: dict[str, int] = {}
        ranks_t2: dict[str, int] = {}
        ranks_sum: dict[str, int] = {}
        for label, left_idx, right_idx in cuts:
            m1 = [[Fraction(0, 1)] * dim_cut for _ in range(dim_cut)]
            m2 = [[Fraction(0, 1)] * dim_cut for _ in range(dim_cut)]
            ms = [[Fraction(0, 1)] * dim_cut for _ in range(dim_cut)]
            for a in range(q):
                for b in range(q):
                    # Term 1 entry: (a, a, b, b)
                    vals1 = [a, a, b, b]
                    r1 = vals1[left_idx[0]] * side + vals1[left_idx[1]]
                    c1 = vals1[right_idx[0]] * side + vals1[right_idx[1]]
                    m1[r1][c1] = Fraction(1, 1)
                    ms[r1][c1] = Fraction(1, 1)
                    # Term 2 entry: (q+a, q+b, q+a, q+b)
                    vals2 = [q + a, q + b, q + a, q + b]
                    r2 = vals2[left_idx[0]] * side + vals2[left_idx[1]]
                    c2 = vals2[right_idx[0]] * side + vals2[right_idx[1]]
                    m2[r2][c2] = Fraction(1, 1)
                    ms[r2][c2] = Fraction(1, 1)
            ranks_t1[label] = _mat_rank_q(m1)
            ranks_t2[label] = _mat_rank_q(m2)
            ranks_sum[label] = _mat_rank_q(ms)

        # Verify each term has rank 1 on its own cut, while T1+T2 has rank >= q^2 + 1 on EVERY balanced cut!
        if ranks_t1["12|34"] != 1 or ranks_t2["13|24"] != 1:
            raise VerificationError("Individual terms failed rank-1 on own balanced cut")
        exp_ranks = _req_dict(cert.get("expected_sum_cut_ranks"), "expected_sum_cut_ranks")
        for label, _, _ in cuts:
            er = _req_int(exp_ranks.get(label), f"expected_sum_cut_ranks.{label}", 1)
            if ranks_sum[label] != er:
                raise VerificationError(f"Cut {label} sum rank {ranks_sum[label]} != expected {er}")
            if ranks_sum[label] <= q * q:
                raise VerificationError(f"Cut {label} sum rank {ranks_sum[label]} not > q^2")

        return {
            "mode": "balanced_cut_and_poincare",
            "submode": submode,
            "wire_dim_q": q,
            "sum_cut_ranks": ranks_sum,
        }

    # submode == "poincare_and_barycentric_smoothing" (Lemma 4.1 & Thm. 4.2)
    n = _req_int(cert.get("num_vertices_n"), "num_vertices_n", 2, MAX_GRAPH_N)
    deg = _req_int(cert.get("degree_d"), "degree_d", 1, MAX_MAT_DIM)
    t_steps = _req_int(cert.get("smoothing_t"), "smoothing_t", 2, 8)
    if t_steps % 2 != 0:
        raise VerificationError("smoothing_t must be even (Lemma 4.1)")
    adj = _req_int_mat(cert.get("adjacency_counts"), "adjacency_counts", rows=n, cols=n)
    for i in range(n):
        row_s = 0
        for j in range(n):
            if adj[i][j] < 0 or adj[i][j] != adj[j][i]:
                raise VerificationError(f"Adjacency not symmetric nonnegative at ({i},{j})")
            row_s += adj[i][j]
        if row_s != deg:
            raise VerificationError(f"Vertex {i} row sum {row_s} != degree_d={deg}")

    dim_e = _req_int(cert.get("embed_dim"), "embed_dim", 1, 6)
    pts_raw = _req_list(cert.get("placement_x"), "placement_x", max_len=n)
    if len(pts_raw) != n:
        raise VerificationError("placement_x length != n")
    pts = [_req_frac_vec(pt, f"placement_x[{i}]", expected_len=dim_e) for i, pt in enumerate(pts_raw)]

    def sq_dist(u: list[Fraction], v: list[Fraction]) -> Fraction:
        return sum(((u[k] - v[k]) ** 2 for k in range(dim_e)), Fraction(0, 1))

    # Walk kernel P = adj / deg, uniform stationary law pi = 1/n
    p_ker = [[Fraction(adj[i][j], deg) for j in range(n)] for i in range(n)]
    inv_n = Fraction(1, n)

    def energy(ker: list[list[Fraction]], pos: list[list[Fraction]]) -> Fraction:
        tot = Fraction(0, 1)
        for i in range(n):
            for j in range(n):
                if ker[i][j] != 0:
                    tot = tot + inv_n * ker[i][j] * sq_dist(pos[i], pos[j])
        return tot

    e_p = energy(p_ker, pts)
    if e_p <= 0:
        raise VerificationError("Non-constant placement required (E_P(x) must be > 0)")
    v_pi = Fraction(0, 1)
    for i in range(n):
        for j in range(n):
            v_pi = v_pi + inv_n * inv_n * sq_dist(pts[i], pts[j])
    beta_val = v_pi * Fraction(e_p.denominator, e_p.numerator)
    exp_beta = _req_frac(cert.get("expected_poincare_ratio"), "expected_poincare_ratio")
    if beta_val != exp_beta:
        raise VerificationError(f"Poincare ratio {beta_val} != expected {exp_beta}")

    # Build A = (I + P)/2 and S = (1/t) * sum_{h=1}^t A^h
    half = Fraction(1, 2)
    a_ker = [
        [half * ((Fraction(1, 1) if i == j else Fraction(0, 1)) + p_ker[i][j]) for j in range(n)]
        for i in range(n)
    ]

    def mat_mul_q(m1: list[list[Fraction]], m2: list[list[Fraction]]) -> list[list[Fraction]]:
        out = [[Fraction(0, 1)] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                s = Fraction(0, 1)
                for k in range(n):
                    s = s + m1[i][k] * m2[k][j]
                out[i][j] = s
        return out

    s_ker = [[Fraction(0, 1)] * n for _ in range(n)]
    cur_pow = a_ker
    inv_t = Fraction(1, t_steps)
    for h_step in range(1, t_steps + 1):
        for i in range(n):
            for j in range(n):
                s_ker[i][j] = s_ker[i][j] + inv_t * cur_pow[i][j]
        if h_step < t_steps:
            cur_pow = mat_mul_q(cur_pow, a_ker)

    e_s = energy(s_ker, pts)

    # Compute exact Lemma 4.1 barycentric iterates x^(g) for 0 <= g < t/2 and verify Eq. (4.1) holds for best g
    cur_x = pts
    best_lhs: Fraction | None = None
    for _g in range(t_steps // 2):
        u_g = inv_n * sum((sq_dist(pts[i], cur_x[i]) for i in range(n)), Fraction(0, 1))
        lhs_g = u_g + Fraction(t_steps, 1) * energy(p_ker, cur_x)
        if best_lhs is None or lhs_g < best_lhs:
            best_lhs = lhs_g
        # Next barycenter x^(g+1)_i = sum_j A_{ij} x^(g)_j
        nxt_x: list[list[Fraction]] = []
        for i in range(n):
            coord = [sum((a_ker[i][j] * cur_x[j][k] for j in range(n)), Fraction(0, 1)) for k in range(dim_e)]
            nxt_x.append(coord)
        cur_x = nxt_x

    if best_lhs is None or best_lhs > Fraction(16, 1) * e_s:
        raise VerificationError(f"Lemma 4.1 Eq. (4.1) failed: best_lhs={best_lhs} > 16*E_S={16 * e_s}")

    return {
        "mode": "balanced_cut_and_poincare",
        "submode": submode,
        "poincare_ratio": [beta_val.numerator, beta_val.denominator],
        "E_P": [e_p.numerator, e_p.denominator],
        "E_S": [e_s.numerator, e_s.denominator],
        "best_smoothing_lhs": [best_lhs.numerator, best_lhs.denominator],
    }


# ---------------------------------------------------------------------------
# Mode 3: cone_savings_and_exterior_minors (Sec. 3.2 Eq. 3.1-3.3, Sec. 8-9)
# ---------------------------------------------------------------------------
def _verify_mode3(cert: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(cert.get("submode"), "submode")
    if submode not in ("cone_cut_supplier_saving", "exterior_minor_tensor"):
        raise VerificationError(f"Unknown Mode 3 submode: {submode!r}")

    if submode == "cone_cut_supplier_saving":
        # Sec. 3.2 Eq. (3.1)-(3.3): d unit sites with Cartan barycenter at 0, balanced cut b_l,
        # suppliers Z_{l,0}, Z_{l,1} at distance <= 1, positive linear saving sum <x_i, Z_{l,b_i}> > 0,
        # and actual squared transport distance reduction at step tau > 0.
        d_rows = _req_int(cert.get("num_rows_d"), "num_rows_d", 4, 16)
        dim_e = _req_int(cert.get("embed_dim"), "embed_dim", 2, 6)
        sites_raw = _req_list(cert.get("unit_sites_x"), "unit_sites_x", max_len=d_rows)
        if len(sites_raw) != d_rows:
            raise VerificationError("unit_sites_x length != num_rows_d")
        sites = [_req_frac_vec(s, f"unit_sites_x[{i}]", expected_len=dim_e) for i, s in enumerate(sites_raw)]

        # Verify unit norms ||x_i||^2 = 1 and Cartan barycenter sum x_i = 0
        for i, x in enumerate(sites):
            nsq = sum((c * c for c in x), Fraction(0, 1))
            if nsq != 1:
                raise VerificationError(f"Site {i} norm squared {nsq} != 1")
        for k in range(dim_e):
            if sum((sites[i][k] for i in range(d_rows)), Fraction(0, 1)) != 0:
                raise VerificationError(f"Cartan barycenter coordinate {k} != 0")

        cut_bits = [_req_int(b, f"balanced_cut[{i}]", 0, 1) for i, b in enumerate(_req_list(cert.get("balanced_cut"), "balanced_cut"))]
        if len(cut_bits) != d_rows:
            raise VerificationError("balanced_cut length != num_rows_d")
        c1 = sum(cut_bits)
        c0 = d_rows - c1
        if 3 * c0 < d_rows or 3 * c1 < d_rows:
            raise VerificationError(f"Cut ({c0},{c1}) is not balanced (require >= d/3 per side)")

        z0 = _req_frac_vec(cert.get("Z_0"), "Z_0", expected_len=dim_e)
        z1 = _req_frac_vec(cert.get("Z_1"), "Z_1", expected_len=dim_e)
        if sum(((z0[k] - z1[k]) ** 2 for k in range(dim_e)), Fraction(0, 1)) > 1:
            raise VerificationError("d(Z_0, Z_1)^2 > 1 violates Sec. 3.2 supplier separation bound")

        tau = _req_frac(cert.get("step_tau"), "step_tau")
        if tau <= 0 or tau > 1:
            raise VerificationError("step_tau must lie in (0, 1]")

        lin_saving = Fraction(0, 1)
        sum_r_sq = Fraction(0, 1)
        for i in range(d_rows):
            z = z1 if cut_bits[i] == 1 else z0
            ip = sum((sites[i][k] * z[k] for k in range(dim_e)), Fraction(0, 1))
            lin_saving = lin_saving + ip
            rsq = sum(((sites[i][k] - tau * z[k]) ** 2 for k in range(dim_e)), Fraction(0, 1))
            sum_r_sq = sum_r_sq + rsq

        if lin_saving <= 0:
            raise VerificationError(f"First-order cut saving {lin_saving} not strictly positive")
        if not (sum_r_sq < Fraction(d_rows, 1)):
            raise VerificationError(f"Transport squared distance sum {sum_r_sq} not < d={d_rows}")
        exp_sav = _req_frac(cert.get("expected_linear_saving"), "expected_linear_saving")
        if lin_saving != exp_sav:
            raise VerificationError(f"expected_linear_saving={exp_sav} != computed {lin_saving}")

        return {
            "mode": "cone_savings_and_exterior_minors",
            "submode": submode,
            "d_rows": d_rows,
            "cut_split": [c0, c1],
            "linear_saving": [lin_saving.numerator, lin_saving.denominator],
            "sum_r_sq": [sum_r_sq.numerator, sum_r_sq.denominator],
        }

    # submode == "exterior_minor_tensor" (Sec. 8-9: k x k minor tensor & Plucker/alternating check over F_p)
    p = _req_int(cert.get("prime_p"), "prime_p", 3, 10007)
    if not _is_prime(p):
        raise VerificationError("prime_p must be prime")
    k_order = _req_int(cert.get("order_k"), "order_k", 2, 3)
    n_cols = _req_int(cert.get("ambient_n"), "ambient_n", k_order + 1, 5)
    v_mat = _req_int_mat(cert.get("basis_matrix_V"), "basis_matrix_V", rows=k_order, cols=n_cols)

    # Enumerate all ordered k-tuples of indices in 0..n_cols-1, compute exact minor det mod p
    nonzero_count = 0
    tuples_list: list[tuple[int, ...]] = []
    cur: list[int] = []

    def gen_t() -> None:
        if len(cur) == k_order:
            tuples_list.append(tuple(cur))
            return
        for c in range(n_cols):
            cur.append(c)
            gen_t()
            cur.pop()

    gen_t()
    minor_val: dict[tuple[int, ...], int] = {}
    for tup in tuples_list:
        sub = [[v_mat[r][tup[c]] % p for c in range(k_order)] for r in range(k_order)]
        d_val = _mat_det_fp(sub, p)
        minor_val[tup] = d_val
        if d_val != 0:
            nonzero_count += 1
    if nonzero_count == 0:
        raise VerificationError("Vacuous zero exterior minor tensor (rank(V) < k)")

    # Verify full S_k alternating symmetry: every adjacent transposition (pos, pos+1) negates the entry mod p
    for tup, val in minor_val.items():
        for pos in range(k_order - 1):
            swapped = tup[:pos] + (tup[pos + 1], tup[pos]) + tup[pos + 2 :]
            if (val + minor_val[swapped]) % p != 0:
                raise VerificationError(f"Alternating symmetry failed at {tup} swap ({pos},{pos+1})")

    # For k=2 and n_cols >= 4, verify Plucker relation p_{a,b}*p_{c,d} - p_{a,c}*p_{b,d} + p_{a,d}*p_{b,c} = 0 mod p
    plucker_checks = 0
    if k_order == 2 and n_cols >= 4:
        for a in range(n_cols):
            for b in range(a + 1, n_cols):
                for c in range(b + 1, n_cols):
                    for d in range(c + 1, n_cols):
                        pl = (
                            minor_val[(a, b)] * minor_val[(c, d)]
                            - minor_val[(a, c)] * minor_val[(b, d)]
                            + minor_val[(a, d)] * minor_val[(b, c)]
                        ) % p
                        if pl != 0:
                            raise VerificationError(f"Plucker relation failed on ({a},{b},{c},{d})")
                        plucker_checks += 1

    exp_nz = _req_int(cert.get("expected_nonzero_entries"), "expected_nonzero_entries", 1)
    if nonzero_count != exp_nz:
        raise VerificationError(f"Nonzero minor entries {nonzero_count} != expected {exp_nz}")

    return {
        "mode": "cone_savings_and_exterior_minors",
        "submode": submode,
        "prime_p": p,
        "order_k": k_order,
        "nonzero_entries": nonzero_count,
        "plucker_checks": plucker_checks,
    }


# ---------------------------------------------------------------------------
# Mode 4: cartier_residue_and_counting_diag (Secs. 18-19, Eq. 19.1-19.2)
# ---------------------------------------------------------------------------
def _verify_mode4(cert: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(cert.get("submode"), "submode")
    if submode not in ("cartier_laurent_residue", "sec19_eigenvalue_contradiction"):
        raise VerificationError(f"Unknown Mode 4 submode: {submode!r}")

    if submode == "cartier_laurent_residue":
        # Sec. 18: Over F_p((t)), Cartier operator C(sum c_k t^k dt) = sum c_{p*m + p - 1} t^m dt (since a^{1/p}=a in F_p).
        # Verify on a Laurent polynomial f(t) = sum_{k=-pole}^{deg} c_k t^k that:
        # 1. C kills all exact derivatives g'(t) dt (C(d(g)) = 0 identically),
        # 2. C(f(t) dt) extracts exact residue c_{-1} at m = -1 (since p*(-1) + p - 1 = -1!) even with higher poles!
        p = _req_int(cert.get("prime_p"), "prime_p", 2, 97)
        if not _is_prime(p):
            raise VerificationError("prime_p must be prime")
        min_exp = _req_int(cert.get("min_exp"), "min_exp", -16, -1)
        coeffs_raw = _req_list(cert.get("laurent_coeffs"), "laurent_coeffs", max_len=40)
        if len(coeffs_raw) < -min_exp + 1:
            raise VerificationError("laurent_coeffs must cover exponent -1 and constant term 0")
        coeffs = [_req_int(c, f"laurent_coeffs[{i}]", 0, p - 1) for i, c in enumerate(coeffs_raw)]
        # Verify non-vacuous pole (some coeff with k <= -2 is nonzero)
        if not any(coeffs[i] != 0 for i in range(-min_exp - 1)):
            raise VerificationError("Vacuous pole-free Laurent series: require at least one pole of order >= 2")

        # Apply Cartier operator C(sum c_k t^k dt): keep k = p*m + (p - 1), map to exponent m
        cartier_out: dict[int, int] = {}
        for idx, c_val in enumerate(coeffs):
            k_exp = min_exp + idx
            if (k_exp - (p - 1)) % p == 0:
                m_exp = (k_exp - (p - 1)) // p
                cartier_out[m_exp] = c_val % p

        res_from_c = cartier_out.get(-1, 0)
        true_res = coeffs[-1 - min_exp] % p
        if res_from_c != true_res:
            raise VerificationError(f"Cartier residue {res_from_c} != c_-1={true_res}")
        exp_res = _req_int(cert.get("expected_residue"), "expected_residue", 1, p - 1)
        if res_from_c != exp_res:
            raise VerificationError(f"expected_residue={exp_res} != {res_from_c}")

        # Verify Cartier kills non-vanishing exact derivative d(g) of supplied Laurent polynomial g
        g_raw = _req_list(cert.get("exact_derivative_poly_g"), "exact_derivative_poly_g", max_len=20)
        if len(g_raw) < 2:
            raise VerificationError("exact_derivative_poly_g must have length >= 2")
        g_coeffs = [_req_int(c, f"g[{i}]", 0, p - 1) for i, c in enumerate(g_raw)]
        if all(c == 0 for c in g_coeffs):
            raise VerificationError("Vacuous zero polynomial g")
        # g(t) = sum g_j t^(min_exp + j) -> g'(t) = sum (min_exp + j) * g_j * t^(min_exp + j - 1)
        deriv_nonzero = False
        for j, gj in enumerate(g_coeffs):
            exp_g = min_exp + j
            deriv_exp = exp_g - 1
            deriv_coeff = (exp_g * gj) % p
            if deriv_coeff != 0:
                deriv_nonzero = True
            if (deriv_exp - (p - 1)) % p == 0 and deriv_coeff != 0:
                raise VerificationError("Cartier operator failed to annihilate exact derivative d(g)")
        if not deriv_nonzero:
            raise VerificationError("Vacuous constant/p-th-power polynomial g: g'(t) is identically zero mod p")

        return {
            "mode": "cartier_residue_and_counting_diag",
            "submode": submode,
            "prime_p": p,
            "extracted_residue": res_from_c,
            "cartier_terms": len(cartier_out),
        }

    # submode == "sec19_eigenvalue_contradiction" (Eq. 19.1-19.2)
    p = _req_int(cert.get("prime_p"), "prime_p", 2, 10007)
    if not _is_prime(p):
        raise VerificationError("prime_p must be prime")
    m = _req_int(cert.get("dim_m"), "dim_m", 2, 8)
    h_star = _req_int(cert.get("H_star"), "H_star", 0, m - 1)
    omega_vec = [_req_int(x, f"Omega[{i}]", 0, p - 1) for i, x in enumerate(_req_list(cert.get("Omega"), "Omega"))]
    z_vec = [_req_int(x, f"Z[{i}]", 0, p - 1) for i, x in enumerate(_req_list(cert.get("Z"), "Z"))]
    if len(omega_vec) != m or len(z_vec) != m:
        raise VerificationError("Omega and Z must have length dim_m")
    if omega_vec[h_star] % p == 0:
        raise VerificationError("Require Omega(H*) != 0 mod p")

    w_list_raw = _req_list(cert.get("W_matrices"), "W_matrices", max_len=m)
    if len(w_list_raw) != m:
        raise VerificationError("W_matrices must contain dim_m matrices (one per H)")
    w_mats = [_req_int_mat(w_list_raw[h_i], f"W_matrices[{h_i}]", rows=m, cols=m) for h_i in range(m)]

    # 1. Verify Eq. (19.1): W(H) * Omega = Z(H) * Omega mod p for EVERY H in 0..m-1
    for h_i in range(m):
        for r in range(m):
            lhs = sum(w_mats[h_i][r][c] * omega_vec[c] for c in range(m)) % p
            rhs = (z_vec[h_i] * omega_vec[r]) % p
            if lhs != rhs:
                raise VerificationError(f"Eq. (19.1) W({h_i})*Omega != Z({h_i})*Omega at row {r}")

    # 2. Compute diagonalized program count P(H) = 1_{H=H*} + sum_I W(I)_{I, H} mod p (Eq. 19.2)
    prog_counts = [
        ((1 if h_i == h_star else 0) + sum(w_mats[i_idx][i_idx][h_i] for i_idx in range(m))) % p
        for h_i in range(m)
    ]

    # 3. Verify exact algebraic trace identity sum_H P(H)*Omega(H) = Omega(H*) + sum_I Z(I)*Omega(I) mod p
    lhs_sum = sum(prog_counts[h_i] * omega_vec[h_i] for h_i in range(m)) % p
    rhs_z_sum = sum(z_vec[i_idx] * omega_vec[i_idx] for i_idx in range(m)) % p
    if lhs_sum != (omega_vec[h_star] + rhs_z_sum) % p:
        raise VerificationError("Eq. (19.2) trace interchange identity failed")

    # 4. Certify that Z == prog_counts is IMPOSSIBLE (specifically lhs_sum - rhs_z_sum = Omega(H*) != 0 mod p)
    gap = (lhs_sum - rhs_z_sum) % p
    if gap != omega_vec[h_star] % p or gap == 0:
        raise VerificationError("Contradiction gap != Omega(H*) mod p")
    if prog_counts == [z % p for z in z_vec]:
        raise VerificationError("Impossible: prog_counts == Z despite Omega(H*) != 0")

    return {
        "mode": "cartier_residue_and_counting_diag",
        "submode": submode,
        "prime_p": p,
        "dim_m": m,
        "H_star": h_star,
        "contradiction_gap_mod_p": gap,
    }


def verify_certificate(cert: Any) -> dict[str, Any]:
    d = _req_dict(cert, "certificate")
    schema = _req_str(d.get("schema"), "schema")
    if schema != SCHEMA_VERSION:
        raise VerificationError(f"Unsupported schema {schema!r}; expected {SCHEMA_VERSION!r}")
    cert_id = _req_str(d.get("certificate_id"), "certificate_id")
    mode = _req_str(d.get("mode"), "mode")
    _req_str(d.get("claim_ref"), "claim_ref")

    if mode == "sparse_gadgets_and_per_hc_det":
        res = _verify_mode1(d)
    elif mode == "balanced_cut_and_poincare":
        res = _verify_mode2(d)
    elif mode == "cone_savings_and_exterior_minors":
        res = _verify_mode3(d)
    elif mode == "cartier_residue_and_counting_diag":
        res = _verify_mode4(d)
    else:
        raise VerificationError(f"Unknown mode: {mode!r}")

    res["certificate_id"] = cert_id
    res["schema"] = schema
    res["status"] = "VERIFIED"
    return res


def verify_file(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    if len(raw) > MAX_JSON_BYTES:
        raise VerificationError(f"Certificate file exceeds MAX_JSON_BYTES ({MAX_JSON_BYTES})")
    try:
        text = raw.decode("utf-8")
        obj = json.loads(
            text,
            object_pairs_hook=_no_dup_pairs,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as exc:
        raise VerificationError(f"Malformed or overly nested JSON: {exc}") from exc
    return verify_certificate(obj)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify PERM-HC-LB-CERT-1.0 certificates.")
    parser.add_argument("paths", nargs="+", type=Path, help="Certificate JSON file(s) or directory")
    args = parser.parse_args(argv)

    files: list[Path] = []
    for p in args.paths:
        if p.is_dir():
            files.extend(sorted(p.glob("*.json")))
        else:
            files.append(p)
    if not files:
        print("No certificate files found.", file=sys.stderr)
        return 2

    ok = 0
    for f in files:
        try:
            summary = verify_file(f)
            print(f"[VERIFIED] {f.name}: {summary['mode']} ({summary.get('submode', 'core')})")
            ok += 1
        except VerificationError as exc:
            print(f"[REJECTED] {f.name}: {exc}", file=sys.stderr)
            return 1
    print(f"Verified {ok}/{len(files)} certificates under {SCHEMA_VERSION}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
