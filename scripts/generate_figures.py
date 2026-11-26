"""Generate 3 publication-quality figures for Paper 70 (PERM-HC-LB-CERT-1.0)."""

from __future__ import annotations

from pathlib import Path
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9,
    "axes.titlesize": 9.5,
    "axes.labelsize": 8.5,
    "legend.fontsize": 7.2,
    "xtick.labelsize": 8,
    "ytick.labelsize": 8,
    "figure.dpi": 300,
})


def make_fig1() -> None:
    """Fig. 1: Mode 1 Sparse Per/Det/HC Separation (C03) & Mode 2 4-Row Balanced-Cut Ranks (C05)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.85))
    fig.subplots_adjust(wspace=0.35, left=0.09, right=0.98, bottom=0.19, top=0.84)

    # Panel (a): C03 3-regular 5-vertex digraph exact values over Q: Per_5, Det_5, HC_5
    # Compute exact values for 5x5 circulant (0,1,2)
    # Per = 13, Det = 3, HC = 2 (we compute directly so figure matches C03 100%!)
    from fractions import Fraction
    import sys
    sys.path.insert(0, str(ROOT))
    from src.perm_hc_verifier import _per_det_hc_frac

    m5 = [
        [Fraction(1), Fraction(1), Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(1), Fraction(1), Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(0), Fraction(1), Fraction(1), Fraction(1)],
        [Fraction(1), Fraction(0), Fraction(0), Fraction(1), Fraction(1)],
        [Fraction(1), Fraction(1), Fraction(0), Fraction(0), Fraction(1)],
    ]
    p5, d5, h5 = _per_det_hc_frac(m5)
    labels = ["$\\mathrm{Per}_5(X)$", "$\\mathrm{Det}_5(X)$", "$\\mathrm{HC}_5(X)$"]
    vals = [int(p5), int(d5), int(h5)]
    cols = ["#4C78A8", "#F58518", "#54A24B"]
    bars = ax1.bar(range(3), vals, color=cols, edgecolor="black", linewidth=0.7, width=0.54)
    for bar, v in zip(bars, vals):
        ax1.text(bar.get_x() + bar.get_width() / 2, v + 0.35, str(v), ha="center", va="bottom", fontsize=8.0, fontweight="bold")
    ax1.set_xticks(range(3))
    ax1.set_xticklabels(labels, fontsize=8.0)
    ax1.set_ylabel("Exact value over $\\mathbb{Q}$")
    ax1.set_ylim(0, max(vals) + 3.2)
    ax1.set_title("(a) Cor. 3.5 Degree-3 Separation (C03)")
    ax1.grid(axis="y", linestyle=":", alpha=0.5)

    # Panel (b): C05 Sec. 1.3 4-row balanced-cut crossing ranks (q=2)
    cuts = ["$12\\mid 34$", "$13\\mid 24$", "$14\\mid 23$"]
    x = np.arange(3)
    w = 0.25
    r_t1 = [1, 4, 4]
    r_t2 = [4, 1, 4]
    r_sum = [5, 5, 8]
    b1 = ax2.bar(x - w, r_t1, width=w, color="#72B7B2", edgecolor="black", linewidth=0.7, label="Term $T_1$")
    b2 = ax2.bar(x, r_t2, width=w, color="#F58518", edgecolor="black", linewidth=0.7, label="Term $T_2$")
    b3 = ax2.bar(x + w, r_sum, width=w, color="#E45756", edgecolor="black", linewidth=0.7, label="Sum $T_1+T_2$")
    for grp in (b1, b2, b3):
        for bar in grp:
            h = int(bar.get_height())
            ax2.text(bar.get_x() + bar.get_width() / 2, h + 0.18, str(h), ha="center", va="bottom", fontsize=7.3, fontweight="bold")
    ax2.set_xticks(x)
    ax2.set_xticklabels(cuts, fontsize=8.0)
    ax2.set_ylabel("Exact $\\mathbb{Q}$-flattening rank")
    ax2.set_ylim(0, 10.5)
    ax2.set_title("(b) Sec. 1.3 Balanced-Cut Ranks (C05)")
    ax2.legend(loc="upper left", frameon=True)
    ax2.grid(axis="y", linestyle=":", alpha=0.5)

    fig.savefig(FIG_DIR / "fig1_sparse_and_balanced_cuts.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig1_sparse_and_balanced_cuts.png", bbox_inches="tight")
    plt.close(fig)


def make_fig2() -> None:
    """Fig. 2: Mode 2 Nonlinear Poincare Ratios (C06-C08) & Mode 3 Cone Cut Savings (C09-C10)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.8))
    fig.subplots_adjust(wspace=0.35, left=0.09, right=0.98, bottom=0.19, top=0.84)

    # Panel (a): Exact Poincare ratios beta = V_pi / E_P across regular graphs C_4, Q_3, C_6
    graphs = ["$C_4$ ($d{=}2$)\nC06", "$Q_3$ ($d{=}3$)\nC08", "$C_6$ ($d{=}2$)\nC07"]
    betas = [1.0, 1.5, 11.0 / 6.0]
    cols = ["#54A24B", "#4C78A8", "#E45756"]
    bars = ax1.bar(range(3), betas, color=cols, edgecolor="black", linewidth=0.7, width=0.52)
    ax1.axhline(0.5, color="#333333", linestyle="--", linewidth=0.95, label="Thm. 4.2 floor $\\beta\\geq 1/2$")
    lbls = ["$1$", "$3/2$", "$11/6$"]
    for bar, v, lbl in zip(bars, betas, lbls):
        ax1.text(bar.get_x() + bar.get_width() / 2, v + 0.06, lbl, ha="center", va="bottom", fontsize=7.8, fontweight="bold")
    ax1.set_xticks(range(3))
    ax1.set_xticklabels(graphs, fontsize=7.8)
    ax1.set_ylabel("Poincaré ratio $\\beta = V_\\pi / E_P$")
    ax1.set_ylim(0, 2.35)
    ax1.set_title("(a) Thm. 4.2 Regular-Graph Poincaré Ratios")
    ax1.legend(loc="upper left", frameon=True)
    ax1.grid(axis="y", linestyle=":", alpha=0.5)

    # Panel (b): Sec. 3.2 Cone supplier transport squared distance sum_i r_i^2 vs tip star benchmark d
    # C09 (d=4, tau=1/2): each r_i^2 = (1 - 1/8)^2 + (1/8)^2 = 49/64 + 1/64 = 50/64 = 25/32 -> sum = 25/8 = 3.125 < 4!
    # C10 (d=6, tau=1/2): each r_i^2 = (7/8)^2 + 2*(1/8)^2 = 51/64 -> sum = 306/64 = 153/32 = 4.78125 < 6!
    x = np.arange(2)
    w = 0.34
    tip = [4.0, 6.0]
    two_sup = [25.0 / 8.0, 153.0 / 32.0]
    b1 = ax2.bar(x - w / 2, tip, width=w, color="#BAB0AC", edgecolor="black", linewidth=0.7, label="Single tip ($d$)")
    b2 = ax2.bar(x + w / 2, two_sup, width=w, color="#4C78A8", edgecolor="black", linewidth=0.7, label="2 suppliers ($\\sum r_i^2$)")
    for b, lbl in zip(b1, ["4.00", "6.00"]):
        ax2.text(b.get_x() + b.get_width() / 2, b.get_height() + 0.16, lbl, ha="center", va="bottom", fontsize=7.6, fontweight="bold")
    for b, lbl in zip(b2, ["3.125", "4.781"]):
        ax2.text(b.get_x() + b.get_width() / 2, b.get_height() + 0.16, lbl, ha="center", va="bottom", fontsize=7.6, fontweight="bold")
    ax2.set_xticks(x)
    ax2.set_xticklabels(["C09 ($d{=}4, \\mathbb{R}^2$)\nSaving $=1$", "C10 ($d{=}6, \\mathbb{R}^3$)\nSaving $=3/2$"], fontsize=7.6)
    ax2.set_ylabel("Total squared leg length")
    ax2.set_ylim(0, 7.6)
    ax2.set_title("(b) Sec. 3.2 Two-Supplier Cut Savings")
    ax2.legend(loc="upper left", frameon=True)
    ax2.grid(axis="y", linestyle=":", alpha=0.5)

    fig.savefig(FIG_DIR / "fig2_poincare_and_cone_savings.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig2_poincare_and_cone_savings.png", bbox_inches="tight")
    plt.close(fig)


def make_fig3() -> None:
    """Fig. 3: Mode 4 Cartier Residue Extraction (C13) & Sec. 19 Counting Contradiction (C15)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.8))
    fig.subplots_adjust(wspace=0.35, left=0.09, right=0.98, bottom=0.19, top=0.84)

    # Panel (a): C13 Laurent coefficients mod 5 from k=-6..4 highlighting Cartier-selected exponents {-6, -1, 4}
    exps = np.arange(-6, 5)
    coeffs = [2, 1, 4, 0, 2, 3, 1, 0, 4, 2, 1]
    cols = ["#E45756" if k == -1 else ("#4C78A8" if (k - 4) % 5 == 0 else "#D0D0D0") for k in exps]
    bars = ax1.bar(exps, coeffs, color=cols, edgecolor="black", linewidth=0.6, width=0.68)
    for k, c in zip(exps, coeffs):
        if c > 0:
            ax1.text(k, c + 0.12, str(c), ha="center", va="bottom", fontsize=7.2, fontweight="bold")
    ax1.annotate(
        "Residue $c_{-1}=3$\n($m=-1$)",
        xy=(-1, 3.35),
        xytext=(-2.45, 4.45),
        fontsize=7.2,
        fontweight="bold",
        color="#B22222",
        arrowprops={"arrowstyle": "->", "lw": 0.85, "color": "#B22222"},
        bbox={"boxstyle": "round,pad=0.2", "fc": "#FFF5F5", "ec": "#E45756", "lw": 0.6},
    )
    ax1.set_xticks(exps)
    ax1.set_xlabel("Laurent exponent $k$")
    ax1.set_ylabel("Coeff. in $\\mathbb{F}_5$")
    ax1.set_ylim(0, 5.85)
    ax1.set_title("(a) Sec. 18 Cartier Residue over $\\mathbb{F}_5$ (C13)")
    ax1.grid(axis="y", linestyle=":", alpha=0.5)

    # Panel (b): C15 Sec. 19 Eq. (19.1)-(19.2) Z(H) vs diagonalized program count P(H) mod 7
    # Compute exact P(H) for C15:
    v7 = [1, 1, 2]
    us = [[1, 2, 3], [3, 1, 4], [2, 5, 1]]
    zs = [4, 2, 5]
    p_cnt = [
        ((1 if h == 1 else 0) + sum(((zs[i] if i == h else 0) + us[i][i] * v7[h]) % 7 for i in range(3))) % 7
        for h in range(3)
    ]
    idx = np.arange(3)
    w = 0.34
    b1 = ax2.bar(idx - w / 2, zs, width=w, color="#4C78A8", edgecolor="black", linewidth=0.7, label="Eigenvalue $Z(H)$")
    b2 = ax2.bar(idx + w / 2, p_cnt, width=w, color="#E45756", edgecolor="black", linewidth=0.7, label="Program count $P(H)$")
    for grp in (b1, b2):
        for bar in grp:
            h = int(bar.get_height())
            ax2.text(bar.get_x() + bar.get_width() / 2, h + 0.16, str(h), ha="center", va="bottom", fontsize=7.6, fontweight="bold")
    ax2.set_xticks(idx)
    ax2.set_xticklabels(["$H=0$", "$H=1$ ($H^*$)", "$H=2$"], fontsize=7.8)
    ax2.set_ylabel("Value mod 7")
    ax2.set_ylim(0, 8.2)
    ax2.set_title("(b) Sec. 19 Counting Contradiction (C15)")
    ax2.legend(loc="upper left", frameon=True)
    ax2.grid(axis="y", linestyle=":", alpha=0.5)

    fig.savefig(FIG_DIR / "fig3_cartier_and_diagonal.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig3_cartier_and_diagonal.png", bbox_inches="tight")
    plt.close(fig)


def main() -> int:
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated 3 figures in paper/figures/.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
