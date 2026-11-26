"""Generate the 16 canonical PERM-HC-LB-CERT-1.0 certificates for Paper 70."""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.perm_hc_verifier import SCHEMA_VERSION, _per_det_hc_frac, verify_certificate


def _f(p: int, q: int = 1) -> list[int]:
    fr = Fraction(p, q)
    return [fr.numerator, fr.denominator]


def build_certificates() -> list[tuple[str, dict]]:
    certs: list[tuple[str, dict]] = []

    # ---- MODE 1: Sparse coupling gadget A & sparse Per/Det/HC evaluations (C01-C04) ----
    gadget_a = [
        [_f(1, 2), _f(1, 2), _f(-1, 2)],
        [_f(-1), _f(-1), _f(1)],
        [_f(1), _f(1), _f(1)],
    ]
    # C01: Lemma 3.4 exact 3x3 permanent coupling gadget over Q
    certs.append((
        "C01_lemma34_coupling_gadget_Q.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C01",
            "mode": "sparse_gadgets_and_per_hc_det",
            "submode": "lemma34_coupling_gadget",
            "claim_ref": "Lemma 3.4 (p. 15): 3x3 permanent coupling gadget A over Q (per(A)=1, four 2x2 minors=0, A_33=1)",
            "field_char": 0,
            "gadget_matrix_A": gadget_a,
        },
    ))

    # C02: Lemma 3.4 exact 3x3 permanent coupling gadget over odd prime field F_7
    certs.append((
        "C02_lemma34_coupling_gadget_F7.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C02",
            "mode": "sparse_gadgets_and_per_hc_det",
            "submode": "lemma34_coupling_gadget",
            "claim_ref": "Lemma 3.4 over F_7: odd-characteristic validity of coupling gadget A (inv(2)=4 mod 7)",
            "field_char": 7,
            "gadget_matrix_A": gadget_a,
        },
    ))

    # C03: Cor. 3.5 degree-<=3 sparse 5-vertex digraph over Q: Per=13, Det=3, HC=2 (all distinct!)
    # Directed 5-cycle (0->1->2->3->4->0) + chords (0->2, 1->3, 2->4, 3->0, 4->1) + diagonal (0->0, 1->1, 2->2, 3->3, 4->4):
    # Every vertex has indegree 3, outdegree 3!
    m5 = [
        [_f(1), _f(1), _f(1), _f(0), _f(0)],
        [_f(0), _f(1), _f(1), _f(1), _f(0)],
        [_f(0), _f(0), _f(1), _f(1), _f(1)],
        [_f(1), _f(0), _f(0), _f(1), _f(1)],
        [_f(1), _f(1), _f(0), _f(0), _f(1)],
    ]
    p5, d5, h5 = _per_det_hc_frac([[Fraction(v[0], v[1]) for v in row] for row in m5])
    certs.append((
        "C03_sparse_deg3_per_det_hc_Q.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C03",
            "mode": "sparse_gadgets_and_per_hc_det",
            "submode": "sparse_per_det_hc",
            "claim_ref": "Sec. 1 & Cor. 3.5: 3-regular 5-vertex digraph over Q separates Per_5, Det_5, and HC_5",
            "order_N": 5,
            "max_degree_bound": 3,
            "field_char": 0,
            "matrix_X": m5,
            "expected_per": [p5.numerator, p5.denominator],
            "expected_det": [d5.numerator, d5.denominator],
            "expected_hc": [h5.numerator, h5.denominator],
            "expect_per_ne_det": True,
        },
    ))

    # C04: Characteristic-2 collapse on 3-regular 4-vertex digraph: Per_4 == Det_4 == 1 mod 2 (and HC_4 == 1 mod 2)
    # 4-vertex circulant (0,1,2 shifts): every row has 3 ones, indeg=outdeg=3.
    m4 = [
        [_f(1), _f(1), _f(1), _f(0)],
        [_f(0), _f(1), _f(1), _f(1)],
        [_f(1), _f(0), _f(1), _f(1)],
        [_f(1), _f(1), _f(0), _f(1)],
    ]
    p4, d4, h4 = _per_det_hc_frac([[Fraction(v[0], v[1]) for v in row] for row in m4])
    certs.append((
        "C04_sparse_deg3_char2_collapse_F2.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C04",
            "mode": "sparse_gadgets_and_per_hc_det",
            "submode": "sparse_per_det_hc",
            "claim_ref": "Sec. 1 over F_2: Per_4 = Det_4 mod 2 on 3-regular 4-vertex digraph while HC_4 is tracked separately",
            "order_N": 4,
            "max_degree_bound": 3,
            "field_char": 2,
            "matrix_X": m4,
            "expected_per": [p4.numerator % 2, 1],
            "expected_det": [d4.numerator % 2, 1],
            "expected_hc": [h4.numerator % 2, 1],
            "expect_per_ne_det": False,
        },
    ))

    # ---- MODE 2: Balanced-cut rank & Nonlinear Poincare / Barycentric smoothing (C05-C08) ----
    # C05: Sec. 1.3 4-row balanced-cut crossing tensor with q=2:
    # T1 has rank 1 on 12|34, rank 4 on 13|24 and 14|23; T2 has rank 1 on 13|24, rank 4 on 12|34 and 14|23.
    # Disjoint local supports => T1 + T2 has ranks: 12|34 -> 1+4=5, 13|24 -> 4+1=5, 14|23 -> 4+4=8!
    certs.append((
        "C05_balanced_cut_4row_q2.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C05",
            "mode": "balanced_cut_and_poincare",
            "submode": "four_row_balanced_cut_rank",
            "claim_ref": "Sec. 1.3 & Lemma 3.3: 4-row sum of rank-1 cut terms achieves ranks (5, 5, 8) > q^2=4 across all balanced cuts",
            "wire_dim_q": 2,
            "expected_sum_cut_ranks": {"12|34": 5, "13|24": 5, "14|23": 8},
        },
    ))

    # C06: Lemma 4.1 & Thm. 4.2 Poincare & smoothing on 4-cycle C_4 (d=2, square placement)
    # Vertices of square in R^2: (0,0),(1,0),(1,1),(0,1).
    # Edge energy E_P = 1 (all edges len 1). Pair variance V_pi = (1/16)*(4*0 + 8*1 + 4*2) = 16/16 = 1! Ratio = 1!
    certs.append((
        "C06_poincare_smoothing_C4_square.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C06",
            "mode": "balanced_cut_and_poincare",
            "submode": "poincare_and_barycentric_smoothing",
            "claim_ref": "Lemma 4.1 & Thm. 4.2: 2-regular C_4 embedded as unit square has exact Poincare ratio 1 and obeys Eq. (4.1)",
            "num_vertices_n": 4,
            "degree_d": 2,
            "smoothing_t": 4,
            "adjacency_counts": [
                [0, 1, 0, 1],
                [1, 0, 1, 0],
                [0, 1, 0, 1],
                [1, 0, 1, 0],
            ],
            "embed_dim": 2,
            "placement_x": [[_f(0), _f(0)], [_f(1), _f(0)], [_f(1), _f(1)], [_f(0), _f(1)]],
            "expected_poincare_ratio": _f(1, 1),
        },
    ))

    # C07: Lemma 4.1 & Thm. 4.2 Poincare & smoothing on 6-cycle C_6 (d=2, 1D linear ramp [0,1,2,3,2,1])
    # Edge sq dists: (0-1)^2=1, (1-2)^2=1, (2-3)^2=1, (3-2)^2=1, (2-1)^2=1, (1-0)^2=1 -> E_P = 1.
    # Values [0,1,2,3,2,1], mean = 9/6 = 3/2, var(X) = (1/6)*((9/4)+(1/4)+(1/4)+(9/4)+(1/4)+(1/4)) = (1/6)*(22/4) = 11/12.
    # V_pi = 2 * Var(X) = 11/6! So Poincare ratio beta = 11/6 > 1!
    certs.append((
        "C07_poincare_smoothing_C6_ramp.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C07",
            "mode": "balanced_cut_and_poincare",
            "submode": "poincare_and_barycentric_smoothing",
            "claim_ref": "Lemma 4.1 & Thm. 4.2: 2-regular C_6 linear ramp has Poincare ratio 11/6 and satisfies Eq. (4.1) at t=6",
            "num_vertices_n": 6,
            "degree_d": 2,
            "smoothing_t": 6,
            "adjacency_counts": [
                [0, 1, 0, 0, 0, 1],
                [1, 0, 1, 0, 0, 0],
                [0, 1, 0, 1, 0, 0],
                [0, 0, 1, 0, 1, 0],
                [0, 0, 0, 1, 0, 1],
                [1, 0, 0, 0, 1, 0],
            ],
            "embed_dim": 1,
            "placement_x": [[_f(0)], [_f(1)], [_f(2)], [_f(3)], [_f(2)], [_f(1)]],
            "expected_poincare_ratio": _f(11, 6),
        },
    ))

    # C08: Lemma 4.1 & Thm. 4.2 on 3-regular cube Q_3 (n=8, d=3, canonical {0,1}^3 embedding)
    # Every edge has sq dist 1 -> E_P = 1. Every coordinate has mean 1/2, var 1/4 -> 3 coords total var 3/4 -> V_pi = 2*(3/4) = 3/2!
    adj_q3 = [[0] * 8 for _ in range(8)]
    pts_q3 = []
    for u in range(8):
        pts_q3.append([_f((u >> 0) & 1), _f((u >> 1) & 1), _f((u >> 2) & 1)])
        for b in range(3):
            adj_q3[u][u ^ (1 << b)] = 1
    certs.append((
        "C08_poincare_smoothing_Q3_cube.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C08",
            "mode": "balanced_cut_and_poincare",
            "submode": "poincare_and_barycentric_smoothing",
            "claim_ref": "Lemma 4.1 & Thm. 4.2: 3-regular hypercube Q_3 has exact Poincare ratio 3/2 and obeys Eq. (4.1) at t=4",
            "num_vertices_n": 8,
            "degree_d": 3,
            "smoothing_t": 4,
            "adjacency_counts": adj_q3,
            "embed_dim": 3,
            "placement_x": pts_q3,
            "expected_poincare_ratio": _f(3, 2),
        },
    ))

    # ---- MODE 3: Hadamard cone cut savings & Exterior minor tensors (C09-C12) ----
    # C09: Sec. 3.2 Eq. (3.1)-(3.3) 4 unit sites in R^2: (1,0), (-1,0), (0,1), (0,-1), barycenter 0.
    # Balanced cut: side 1 = {(1,0), (0,1)}, side 0 = {(-1,0), (0,-1)}.
    # Suppliers Z_1 = (1/4, 1/4), Z_0 = (-1/4, -1/4): d(Z_0, Z_1)^2 = (1/2)^2 + (1/2)^2 = 1/2 <= 1!
    # Linear saving = 4 * (1/4) = 1 > 0! At tau=1/2: sum r_i^2 < 4!
    certs.append((
        "C09_cone_cut_savings_d4_R2.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C09",
            "mode": "cone_savings_and_exterior_minors",
            "submode": "cone_cut_supplier_saving",
            "claim_ref": "Sec. 3.2 Eq. (3.1)-(3.3): d=4 unit sites in R^2 with balanced 2|2 cut achieve linear saving 1",
            "num_rows_d": 4,
            "embed_dim": 2,
            "unit_sites_x": [[_f(1), _f(0)], [_f(-1), _f(0)], [_f(0), _f(1)], [_f(0), _f(-1)]],
            "balanced_cut": [1, 0, 1, 0],
            "Z_0": [_f(-1, 4), _f(-1, 4)],
            "Z_1": [_f(1, 4), _f(1, 4)],
            "step_tau": _f(1, 2),
            "expected_linear_saving": _f(1, 1),
        },
    ))

    # C10: Sec. 3.2 Eq. (3.1)-(3.3) d=6 unit sites in R^3 (octahedron +-e1, +-e2, +-e3), balanced 3|3 cut!
    # Side 1 = {+e1, +e2, +e3}, side 0 = {-e1, -e2, -e3}.
    # Suppliers Z_1 = (1/4, 1/4, 1/4), Z_0 = (-1/4, -1/4, -1/4): d(Z_0, Z_1)^2 = 3/4 <= 1!
    # Linear saving = 6 * (1/4) = 3/2!
    certs.append((
        "C10_cone_cut_savings_d6_R3.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C10",
            "mode": "cone_savings_and_exterior_minors",
            "submode": "cone_cut_supplier_saving",
            "claim_ref": "Sec. 3.2 Eq. (3.1)-(3.3): d=6 octahedron sites in R^3 with balanced 3|3 cut achieve linear saving 3/2",
            "num_rows_d": 6,
            "embed_dim": 3,
            "unit_sites_x": [
                [_f(1), _f(0), _f(0)], [_f(-1), _f(0), _f(0)],
                [_f(0), _f(1), _f(0)], [_f(0), _f(-1), _f(0)],
                [_f(0), _f(0), _f(1)], [_f(0), _f(0), _f(-1)],
            ],
            "balanced_cut": [1, 0, 1, 0, 1, 0],
            "Z_0": [_f(-1, 4), _f(-1, 4), _f(-1, 4)],
            "Z_1": [_f(1, 4), _f(1, 4), _f(1, 4)],
            "step_tau": _f(1, 2),
            "expected_linear_saving": _f(3, 2),
        },
    ))

    # C11: Sec. 8-9 exterior minor tensor (k=2, n=4 over F_7): all 6 unordered 2-subsets nonzero -> 12 ordered entries, Plucker=0!
    certs.append((
        "C11_exterior_minor_k2_n4_F7.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C11",
            "mode": "cone_savings_and_exterior_minors",
            "submode": "exterior_minor_tensor",
            "claim_ref": "Sec. 8-9: 2x4 basis over F_7 yields 12 alternating nonzero minors satisfying Plucker relation",
            "prime_p": 7,
            "order_k": 2,
            "ambient_n": 4,
            "basis_matrix_V": [[1, 1, 1, 1], [1, 2, 3, 4]],
            "expected_nonzero_entries": 12,
        },
    ))

    # C12: Sec. 8-9 exterior 3-minor tensor (k=3, n=4 over F_11): 4 unordered 3-subsets -> 4*6 = 24 nonzero alternating entries!
    certs.append((
        "C12_exterior_minor_k3_n4_F11.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C12",
            "mode": "cone_savings_and_exterior_minors",
            "submode": "exterior_minor_tensor",
            "claim_ref": "Sec. 8-9: 3x4 Vandermonde basis over F_11 yields 24 alternating nonzero 3x3 minors",
            "prime_p": 11,
            "order_k": 3,
            "ambient_n": 4,
            "basis_matrix_V": [[1, 1, 1, 1], [1, 2, 3, 4], [1, 4, 9, 5]],
            "expected_nonzero_entries": 24,
        },
    ))

    # ---- MODE 4: Cartier residue extraction & Sec. 19 eigenvalue counting contradiction (C13-C16) ----
    # C13: Sec. 18 Cartier operator over F_5 on Laurent series with pole t^{-6}:
    # min_exp=-6, coeffs for k=-6,-5,-4,-3,-2,-1,0,1,2,3,4:
    # residue c_{-1} = 3; Cartier keeps k in {-6, -1, 4} -> m in {-2, -1, 0}!
    # And kills exact derivative d(g) for g(t) = 2 t^{-6} + 4 t^{-4} + t^{-1} + 3 t^2!
    certs.append((
        "C13_cartier_laurent_residue_F5.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C13",
            "mode": "cartier_residue_and_counting_diag",
            "submode": "cartier_laurent_residue",
            "claim_ref": "Sec. 18 over F_5: Cartier operator kills d(g) and extracts exact residue c_{-1}=3 despite order-6 pole",
            "prime_p": 5,
            "min_exp": -6,
            "laurent_coeffs": [2, 1, 4, 0, 2, 3, 1, 0, 4, 2, 1],
            "expected_residue": 3,
            "exact_derivative_poly_g": [2, 0, 4, 0, 0, 1, 0, 0, 3],
        },
    ))

    # C14: Sec. 18 Cartier operator over F_2 (char-2 valid for HC_N!) with pole t^{-4}, residue c_{-1}=1
    certs.append((
        "C14_cartier_laurent_residue_F2.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C14",
            "mode": "cartier_residue_and_counting_diag",
            "submode": "cartier_laurent_residue",
            "claim_ref": "Sec. 18 over F_2: characteristic-2 Cartier operator kills d(g) and extracts residue c_{-1}=1 for HC_N",
            "prime_p": 2,
            "min_exp": -4,
            "laurent_coeffs": [1, 1, 0, 1, 1, 0, 1],
            "expected_residue": 1,
            "exact_derivative_poly_g": [1, 1, 1, 0, 1],
        },
    ))

    # C15: Sec. 19 Eq. (19.1)-(19.2) counting diagonalization contradiction over F_7 (dim m=3, H*=1)
    # Choose Omega = [2, 3, 1] (Omega[1] = 3 != 0 mod 7), Z = [4, 2, 5].
    # Construct non-diagonal W(H) with W(H)*Omega = Z(H)*Omega mod 7:
    # For any matrix M with row sums matching Z(H)*Omega[r]:
    # Start with W(H) = Z(H)*I + u_H * v^T where v dot Omega = 0 mod 7!
    # Take v = [1, 1, 2]: v dot Omega = 1*2 + 1*3 + 2*1 = 7 = 0 mod 7!!
    def make_w_mat(z_val: int, u_vec: list[int], v_vec: list[int], p: int) -> list[list[int]]:
        m_d = len(u_vec)
        return [
            [((z_val if r == c else 0) + u_vec[r] * v_vec[c]) % p for c in range(m_d)]
            for r in range(m_d)
        ]

    v7 = [1, 1, 2]
    certs.append((
        "C15_sec19_eigenvalue_contradiction_F7.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C15",
            "mode": "cartier_residue_and_counting_diag",
            "submode": "sec19_eigenvalue_contradiction",
            "claim_ref": "Sec. 19 Eq. (19.1)-(19.2) over F_7: non-diagonal W(H)*Omega = Z(H)*Omega forces contradiction gap Omega(H*)=3 != 0",
            "prime_p": 7,
            "dim_m": 3,
            "H_star": 1,
            "Omega": [2, 3, 1],
            "Z": [4, 2, 5],
            "W_matrices": [
                make_w_mat(4, [1, 2, 3], v7, 7),
                make_w_mat(2, [3, 1, 4], v7, 7),
                make_w_mat(5, [2, 5, 1], v7, 7),
            ],
        },
    ))

    # C16: Sec. 19 Eq. (19.1)-(19.2) counting diagonalization contradiction over F_2 (dim m=4, H*=2 -> HC_N in char 2!)
    # Omega = [1, 1, 1, 1] (Omega[2]=1 != 0 mod 2), v = [1, 1, 0, 0] (v dot Omega = 0 mod 2), Z = [1, 0, 1, 0]
    v2 = [1, 1, 0, 0]
    certs.append((
        "C16_sec19_eigenvalue_contradiction_F2.json",
        {
            "schema": SCHEMA_VERSION,
            "certificate_id": "C16",
            "mode": "cartier_residue_and_counting_diag",
            "submode": "sec19_eigenvalue_contradiction",
            "claim_ref": "Sec. 19 Eq. (19.1)-(19.2) over F_2: char-2 diagonalization forces contradiction gap Omega(H*)=1 != 0",
            "prime_p": 2,
            "dim_m": 4,
            "H_star": 2,
            "Omega": [1, 1, 1, 1],
            "Z": [1, 0, 1, 0],
            "W_matrices": [
                make_w_mat(1, [1, 0, 1, 0], v2, 2),
                make_w_mat(0, [0, 1, 0, 1], v2, 2),
                make_w_mat(1, [1, 1, 0, 1], v2, 2),
                make_w_mat(0, [0, 1, 1, 0], v2, 2),
            ],
        },
    ))

    return certs


def main() -> int:
    out_dir = ROOT / "certificates"
    out_dir.mkdir(parents=True, exist_ok=True)
    for old in out_dir.glob("*.json"):
        old.unlink()
    certs = build_certificates()
    for fname, cert in certs:
        res = verify_certificate(cert)
        (out_dir / fname).write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        print(f"Generated & verified {fname}: {res['mode']} ({res.get('submode', 'core')})")
    print(f"Total certificates generated: {len(certs)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
