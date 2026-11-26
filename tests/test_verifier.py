"""Comprehensive pytest & adversarial forgery suite for PERM-HC-LB-CERT-1.0."""

from __future__ import annotations

import ast
import json
from pathlib import Path
import sys
import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.perm_hc_verifier import (
    MAX_JSON_BYTES,
    SCHEMA_VERSION,
    VerificationError,
    verify_certificate,
    verify_file,
)

CERT_DIR = ROOT / "certificates"


def _load(name: str) -> dict:
    return json.loads((CERT_DIR / name).read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# 1. Static AST Hygiene & All 16 Canonical Certificates
# ---------------------------------------------------------------------------
def test_zero_float_and_no_div_ast_hygiene() -> None:
    src_path = ROOT / "src" / "perm_hc_verifier.py"
    tree = ast.parse(src_path.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        assert not isinstance(node, ast.Div), "True division (/) forbidden"
        if isinstance(node, ast.AugAssign):
            assert not isinstance(node.op, ast.Div), "/= forbidden"
        if isinstance(node, ast.Constant):
            assert not isinstance(node.value, float), "Float literal forbidden"
        if isinstance(node, ast.Import):
            for alias in node.names:
                assert alias.name != "math", "math module forbidden"
        if isinstance(node, ast.ImportFrom):
            assert node.module != "math", "math module forbidden"
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            assert node.func.id != "float", "float() call forbidden"


@pytest.mark.parametrize("cert_path", sorted(CERT_DIR.glob("*.json")), ids=lambda p: p.name)
def test_all_canonical_certificates_verify(cert_path: Path) -> None:
    res = verify_file(cert_path)
    assert res["status"] == "VERIFIED"
    assert res["schema"] == SCHEMA_VERSION


def test_exact_certificate_count() -> None:
    assert len(list(CERT_DIR.glob("*.json"))) == 16


# ---------------------------------------------------------------------------
# 2. Structural / JSON / Rational Forgeries
# ---------------------------------------------------------------------------
def test_reject_wrong_schema() -> None:
    c = _load("C01_lemma34_coupling_gadget_Q.json")
    c["schema"] = "WRONG-1.0"
    with pytest.raises(VerificationError, match="Unsupported schema"):
        verify_certificate(c)


def test_reject_unknown_mode() -> None:
    c = _load("C01_lemma34_coupling_gadget_Q.json")
    c["mode"] = "bogus_mode"
    with pytest.raises(VerificationError, match="Unknown mode"):
        verify_certificate(c)


def test_reject_duplicate_json_key(tmp_path: Path) -> None:
    p = tmp_path / "dup.json"
    p.write_text('{"schema":"PERM-HC-LB-CERT-1.0","schema":"PERM-HC-LB-CERT-1.0"}', encoding="utf-8")
    with pytest.raises(VerificationError, match="Duplicate JSON key"):
        verify_file(p)


def test_reject_oversized_json(tmp_path: Path) -> None:
    p = tmp_path / "big.json"
    p.write_bytes(b" " * (MAX_JSON_BYTES + 1))
    with pytest.raises(VerificationError, match="MAX_JSON_BYTES"):
        verify_file(p)


def test_reject_non_lowest_terms_rational() -> None:
    c = _load("C01_lemma34_coupling_gadget_Q.json")
    c["gadget_matrix_A"][0][0] = [2, 4]
    with pytest.raises(VerificationError, match="lowest terms"):
        verify_certificate(c)


def test_reject_zero_denominator() -> None:
    c = _load("C01_lemma34_coupling_gadget_Q.json")
    c["gadget_matrix_A"][0][0] = [1, 0]
    with pytest.raises(VerificationError, match="< 1"):
        verify_certificate(c)


def test_reject_bool_as_int() -> None:
    c = _load("C03_sparse_deg3_per_det_hc_Q.json")
    c["order_N"] = True
    with pytest.raises(VerificationError, match="must be an integer"):
        verify_certificate(c)


def test_reject_whitespace_string() -> None:
    c = _load("C01_lemma34_coupling_gadget_Q.json")
    c["claim_ref"] = "   "
    with pytest.raises(VerificationError, match="non-empty string"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 3. Mode 1 Forgeries (Lemma 3.4 Gadget & Sparse Per/Det/HC)
# ---------------------------------------------------------------------------
def test_mode1_reject_gadget_in_char_2() -> None:
    c = _load("C01_lemma34_coupling_gadget_Q.json")
    c["field_char"] = 2
    with pytest.raises(VerificationError, match="requires char != 2"):
        verify_certificate(c)


def test_mode1_reject_gadget_composite_char() -> None:
    c = _load("C02_lemma34_coupling_gadget_F7.json")
    c["field_char"] = 9
    with pytest.raises(VerificationError, match="requires char != 2"):
        verify_certificate(c)


def test_mode1_reject_gadget_perturbed_entry() -> None:
    c = _load("C01_lemma34_coupling_gadget_Q.json")
    c["gadget_matrix_A"][0][0] = [1, 1]
    with pytest.raises(VerificationError, match="Deleting"):
        verify_certificate(c)


def test_mode1_reject_gadget_bad_A33() -> None:
    # A'' = [[1/4, 1/4, -1/4], [-1, -1, 1], [2, 2, 2]] has per(A'')=1 and all four 2x2 minors=0,
    # directly triggering the A[2][2] != 1 check!
    c = _load("C01_lemma34_coupling_gadget_Q.json")
    c["gadget_matrix_A"] = [
        [[1, 4], [1, 4], [-1, 4]],
        [[-1, 1], [-1, 1], [1, 1]],
        [[2, 1], [2, 1], [2, 1]],
    ]
    with pytest.raises(VerificationError, match="A\\[2\\]\\[2\\]=2 != 1"):
        verify_certificate(c)


def test_mode1_reject_fp_pole_in_gadget_and_sparse_matrix() -> None:
    # B2 exploit 1: 1/14 pole in F_7 gadget must be rejected BEFORE permanent computation
    c1 = _load("C02_lemma34_coupling_gadget_F7.json")
    c1["gadget_matrix_A"] = [
        [[1, 2], [1, 14], [-1, 14]],
        [[-7, 1], [-1, 1], [1, 1]],
        [[7, 1], [1, 1], [1, 1]],
    ]
    with pytest.raises(VerificationError, match="pole in F_7"):
        verify_certificate(c1)

    # B2 exploit 2: 1/2 pole in F_2 sparse matrix must be rejected BEFORE HC computation
    c2 = {
        "schema": SCHEMA_VERSION,
        "certificate_id": "POLE2",
        "mode": "sparse_gadgets_and_per_hc_det",
        "submode": "sparse_per_det_hc",
        "claim_ref": "pole exploit in F_2",
        "order_N": 2,
        "max_degree_bound": 2,
        "field_char": 2,
        "matrix_X": [[[1, 1], [1, 2]], [[2, 1], [1, 1]]],
        "expected_per": [0, 1],
        "expected_det": [0, 1],
        "expected_hc": [1, 1],
        "expect_per_ne_det": False,
    }
    with pytest.raises(VerificationError, match="pole in F_2"):
        verify_certificate(c2)


def test_mode1_reject_all_zero_matrix_and_composite_char() -> None:
    c = _load("C04_sparse_deg3_char2_collapse_F2.json")
    c["matrix_X"] = [[[0, 1]] * 4 for _ in range(4)]
    with pytest.raises(VerificationError, match="Vacuous all-zero"):
        verify_certificate(c)
    c2 = _load("C04_sparse_deg3_char2_collapse_F2.json")
    c2["field_char"] = 6
    with pytest.raises(VerificationError, match="must be 0 or prime"):
        verify_certificate(c2)


def test_mode1_reject_degree_exceeds_3() -> None:
    c = _load("C03_sparse_deg3_per_det_hc_Q.json")
    c["matrix_X"][0][3] = [1, 1]
    with pytest.raises(VerificationError, match="degree.*exceeds 3"):
        verify_certificate(c)


def test_mode1_reject_spoofed_per_det_hc() -> None:
    c = _load("C03_sparse_deg3_per_det_hc_Q.json")
    c["expected_hc"] = [99, 1]
    with pytest.raises(VerificationError, match="\\(Per,Det,HC\\)"):
        verify_certificate(c)


def test_mode1_reject_false_per_ne_det_in_char_2() -> None:
    c = _load("C04_sparse_deg3_char2_collapse_F2.json")
    c["expect_per_ne_det"] = True
    with pytest.raises(VerificationError, match="Expected Per_N != Det_N"):
        verify_certificate(c)


def test_mode1_reject_false_per_eq_det_over_Q() -> None:
    c = _load("C03_sparse_deg3_per_det_hc_Q.json")
    c["expect_per_ne_det"] = False
    with pytest.raises(VerificationError, match="Expected Per_N == Det_N"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 4. Mode 2 Forgeries (Balanced Cuts & Poincare Smoothing)
# ---------------------------------------------------------------------------
def test_mode2_reject_wrong_sum_cut_rank() -> None:
    c = _load("C05_balanced_cut_4row_q2.json")
    c["expected_sum_cut_ranks"]["14|23"] = 7
    with pytest.raises(VerificationError, match="Cut 14\\|23 sum rank 8 != expected 7"):
        verify_certificate(c)


def test_mode2_reject_odd_smoothing_t() -> None:
    c = _load("C06_poincare_smoothing_C4_square.json")
    c["smoothing_t"] = 3
    with pytest.raises(VerificationError, match="must be even"):
        verify_certificate(c)


def test_mode2_reject_asymmetric_adjacency() -> None:
    c = _load("C06_poincare_smoothing_C4_square.json")
    c["adjacency_counts"][0][1] = 2
    with pytest.raises(VerificationError, match="not symmetric"):
        verify_certificate(c)


def test_mode2_reject_non_regular_graph() -> None:
    c = _load("C06_poincare_smoothing_C4_square.json")
    c["adjacency_counts"][0][0] = 1
    with pytest.raises(VerificationError, match="row sum 3 != degree_d=2"):
        verify_certificate(c)


def test_mode2_reject_constant_placement() -> None:
    c = _load("C06_poincare_smoothing_C4_square.json")
    c["placement_x"] = [[[0, 1], [0, 1]]] * 4
    with pytest.raises(VerificationError, match="Non-constant placement"):
        verify_certificate(c)


def test_mode2_accept_q3_four_row_balanced_cut() -> None:
    # B3.4: q=3 with MAX_MAT_DIM=36 now verifies cleanly with ranks (10, 10, 18) > 9!
    c = {
        "schema": SCHEMA_VERSION,
        "certificate_id": "Q3CUT",
        "mode": "balanced_cut_and_poincare",
        "submode": "four_row_balanced_cut_rank",
        "claim_ref": "q=3 balanced-cut ranks (10,10,18)",
        "wire_dim_q": 3,
        "expected_sum_cut_ranks": {"12|34": 10, "13|24": 10, "14|23": 18},
    }
    assert verify_certificate(c)["status"] == "VERIFIED"


def test_mode2_reject_spoofed_poincare_ratio() -> None:
    c = _load("C07_poincare_smoothing_C6_ramp.json")
    c["expected_poincare_ratio"] = [2, 1]
    with pytest.raises(VerificationError, match="Poincare ratio"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 5. Mode 3 Forgeries (Cone Cut Savings & Exterior Minors)
# ---------------------------------------------------------------------------
def test_mode3_reject_non_unit_site() -> None:
    c = _load("C09_cone_cut_savings_d4_R2.json")
    c["unit_sites_x"][0] = [[2, 1], [0, 1]]
    with pytest.raises(VerificationError, match="norm squared 4 != 1"):
        verify_certificate(c)


def test_mode3_reject_nonzero_barycenter() -> None:
    c = _load("C09_cone_cut_savings_d4_R2.json")
    c["unit_sites_x"][1] = [[1, 1], [0, 1]]
    with pytest.raises(VerificationError, match="Cartan barycenter"):
        verify_certificate(c)


def test_mode3_reject_unbalanced_cut() -> None:
    c = _load("C09_cone_cut_savings_d4_R2.json")
    c["balanced_cut"] = [1, 1, 1, 0]
    with pytest.raises(VerificationError, match="not balanced"):
        verify_certificate(c)


def test_mode3_reject_suppliers_too_far_apart() -> None:
    c = _load("C09_cone_cut_savings_d4_R2.json")
    c["Z_0"] = [[-1, 1], [0, 1]]
    c["Z_1"] = [[1, 1], [0, 1]]
    with pytest.raises(VerificationError, match="d\\(Z_0, Z_1\\)\\^2 > 1"):
        verify_certificate(c)


def test_mode3_reject_nonpositive_linear_saving() -> None:
    c = _load("C09_cone_cut_savings_d4_R2.json")
    c["Z_0"], c["Z_1"] = c["Z_1"], c["Z_0"]
    with pytest.raises(VerificationError, match="not strictly positive"):
        verify_certificate(c)


def test_mode3_reject_spoofed_linear_saving() -> None:
    c = _load("C10_cone_cut_savings_d6_R3.json")
    c["expected_linear_saving"] = [2, 1]
    with pytest.raises(VerificationError, match="expected_linear_saving"):
        verify_certificate(c)


def test_mode3_reject_rank_deficient_minor_basis() -> None:
    c = _load("C11_exterior_minor_k2_n4_F7.json")
    c["basis_matrix_V"] = [[1, 1, 1, 1], [2, 2, 2, 2]]
    with pytest.raises(VerificationError, match="Vacuous zero exterior minor"):
        verify_certificate(c)


def test_mode3_reject_wrong_nonzero_minor_count() -> None:
    c = _load("C12_exterior_minor_k3_n4_F11.json")
    c["expected_nonzero_entries"] = 20
    with pytest.raises(VerificationError, match="Nonzero minor entries 24 != expected 20"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 6. Mode 4 Forgeries (Cartier Residue & Sec. 19 Counting Contradiction)
# ---------------------------------------------------------------------------
def test_mode4_reject_pole_free_laurent() -> None:
    c = _load("C13_cartier_laurent_residue_F5.json")
    c["laurent_coeffs"] = [0, 0, 0, 0, 0, 3, 1, 0, 4, 2, 1]
    with pytest.raises(VerificationError, match="Vacuous pole-free"):
        verify_certificate(c)


def test_mode4_reject_spoofed_cartier_residue() -> None:
    c = _load("C13_cartier_laurent_residue_F5.json")
    c["expected_residue"] = 4
    with pytest.raises(VerificationError, match="expected_residue=4 != 3"):
        verify_certificate(c)


def test_mode4_reject_vacuous_zero_g_poly() -> None:
    c = _load("C14_cartier_laurent_residue_F2.json")
    c["exact_derivative_poly_g"] = [0, 0, 0, 0, 0]
    with pytest.raises(VerificationError, match="Vacuous zero polynomial g"):
        verify_certificate(c)


def test_mode4_reject_zero_omega_Hstar() -> None:
    c = _load("C15_sec19_eigenvalue_contradiction_F7.json")
    c["Omega"][1] = 0
    with pytest.raises(VerificationError, match="Omega\\(H\\*\\) != 0"):
        verify_certificate(c)


def test_mode4_reject_broken_eigenvector_eq191() -> None:
    c = _load("C15_sec19_eigenvalue_contradiction_F7.json")
    c["W_matrices"][0][0][0] = (c["W_matrices"][0][0][0] + 1) % 7
    with pytest.raises(VerificationError, match="Eq. \\(19.1\\)"):
        verify_certificate(c)


def test_mode4_reject_composite_prime_in_mode4() -> None:
    c = _load("C16_sec19_eigenvalue_contradiction_F2.json")
    c["prime_p"] = 4
    with pytest.raises(VerificationError, match="must be prime"):
        verify_certificate(c)


# ---------------------------------------------------------------------------
# 7. Additional B3, P3, P4 Soundness & Coverage Tests
# ---------------------------------------------------------------------------
def test_mode4_reject_vanishing_derivative_g_and_zero_residue() -> None:
    # g(t) = 1*t^{-5} over F_5 has g'(t) = -5*t^{-6} = 0 mod 5 identically -> must be rejected!
    c = _load("C13_cartier_laurent_residue_F5.json")
    c["exact_derivative_poly_g"] = [0, 1, 0, 0, 0, 0, 1]  # exponents -5 and 0 -> both derivs 0 mod 5!
    with pytest.raises(VerificationError, match="identically zero mod p"):
        verify_certificate(c)
    c2 = _load("C13_cartier_laurent_residue_F5.json")
    c2["laurent_coeffs"][5] = 0
    c2["expected_residue"] = 0
    with pytest.raises(VerificationError, match="< 1"):
        verify_certificate(c2)


def test_mode3_extra_forgeries_and_submodes() -> None:
    c = _load("C09_cone_cut_savings_d4_R2.json")
    c["step_tau"] = [0, 1]
    with pytest.raises(VerificationError, match="step_tau must lie in"):
        verify_certificate(c)
    c2 = _load("C11_exterior_minor_k2_n4_F7.json")
    c2["prime_p"] = 2
    with pytest.raises(VerificationError, match="< 3"):
        verify_certificate(c2)
    c3 = _load("C11_exterior_minor_k2_n4_F7.json")
    c3["prime_p"] = 9
    with pytest.raises(VerificationError, match="must be prime"):
        verify_certificate(c3)
    for fname in [
        "C01_lemma34_coupling_gadget_Q.json",
        "C05_balanced_cut_4row_q2.json",
        "C09_cone_cut_savings_d4_R2.json",
        "C13_cartier_laurent_residue_F5.json",
    ]:
        cx = _load(fname)
        cx["submode"] = "bogus"
        with pytest.raises(VerificationError, match="Unknown Mode"):
            verify_certificate(cx)


def test_reject_nan_and_recursion_json(tmp_path: Path) -> None:
    p1 = tmp_path / "nan.json"
    p1.write_text('{"schema":"PERM-HC-LB-CERT-1.0","x":NaN}', encoding="utf-8")
    with pytest.raises(VerificationError, match="Non-standard JSON constant"):
        verify_file(p1)
    p2 = tmp_path / "deep.json"
    p2.write_text("[" * 4000 + "]" * 4000, encoding="utf-8")
    with pytest.raises(VerificationError, match="Malformed or overly nested JSON"):
        verify_file(p2)
