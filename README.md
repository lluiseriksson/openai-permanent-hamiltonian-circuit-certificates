# PERM-HC-LB-CERT-1.0: Constructive Algebraic, Poincaré, and Cartier-Residue Certificates for Permanent and Hamiltonian Cycle Circuit Lower Bounds

**Author:** Lluis Eriksson (`lluis@airr.science`)  
**Schema:** `PERM-HC-LB-CERT-1.0`  
**Target Preprint:** OpenAI, *"Circuit lower bounds for Hamiltonian cycle and the permanent"* (`OAI:Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026`, unrefereed preprint, November 24, 2026).

## Overview
This repository provides an independently reproducible, zero-floating-point Python verification engine (`src/perm_hc_verifier.py`), a constructive Lean 4.35.0 kernel (`lean/PermHcLbCert.lean`, 18 constructive theorems, 0 `sorry`, 0 custom axioms, 0 `Classical.choice`, 0 warnings), 16 canonical JSON certificates (`certificates/C01..C16`), 60 unit and adversarial forgery tests (`tests/test_verifier.py`), 3 publication figures, and a 4-page LaTeX/PDF companion paper (`paper/main.pdf`).

## Quick Reproduction
```bash
cd lean && lake build && cd ..
python -m src.perm_hc_verifier certificates/
pytest -q
python scripts/build_manifest.py --check
```

## Licenses & Disclosure
- Manuscript & figures: `CC-BY-4.0`
- Code, Lean proofs & certificates: `MIT`
- Produced with Google Antigravity assistance; independently compiled, verified, and reviewed by Lluis Eriksson.
