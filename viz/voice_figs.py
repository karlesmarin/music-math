# Author: Carles Marin <karlesmarin@gmail.com> (with Claude, Anthropic, as assistant)
# Reusable matplotlib toolkit reproducing Emmanuel Amiot's DFT-of-music figure STYLES
# (camembert, Fourier profile, clock-vector sum, phase torus, pc-clock, phase plane,
#  signature heatmap, Dirichlet kernel; cf. his DFTbv survey), applied to OUR per-voice
# Fourier-character corpus result: mean normalized Fourier characters
# alpha_k = |a_k|/|a_0| (k=1..6) for the 4 SATB voices (by register rank) over the
# Bach 4-part chorales and over Palestrina.
#
# Run:  python voice_figs.py
# Output: exceptional-quality color PNG (300 dpi) + vector PDF in this directory (figs/).

import os
import warnings
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch

warnings.filterwarnings("ignore")

HERE = os.path.dirname(os.path.abspath(__file__))

# --------------------------------------------------------------------------- #
# Global typography / quality settings (serif text + Computer-Modern math).
# --------------------------------------------------------------------------- #
plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["DejaVu Serif"],
    "mathtext.fontset": "cm",
    "axes.titlesize": 14,
    "axes.labelsize": 12,
    "axes.linewidth": 0.9,
    "xtick.labelsize": 10,
    "ytick.labelsize": 10,
    "legend.fontsize": 11,
    "figure.dpi": 120,
    "savefig.dpi": 300,
    "savefig.bbox": "tight",
})

# --------------------------------------------------------------------------- #
# Amiot's 6-character legend + colorblind-reasonable palette.
# a_k named by the maximally-even / periodic subset whose DFT it detects.
# --------------------------------------------------------------------------- #
CHAR_NAMES = [
    r"$a_1$ chromatic",
    r"$a_2$ quartal",
    r"$a_3$ augmented",
    r"$a_4$ octatonic",
    r"$a_5$ diatonic",
    r"$a_6$ whole-tone",
]
# purple / blue / green / olive / orange / red
CHAR_COLORS = ["#7b3fa0", "#2c6fbb", "#3a9b4e", "#9a9a26", "#e08214", "#d6322c"]
VOICE_NAMES = ["Bass", "Tenor", "Alto", "Soprano"]
VOICE_COLORS = ["#1b3a6b", "#2c8a3a", "#d98800", "#b02020"]
VOICE_MARKERS = ["o", "s", "^", "D"]
NOTE_NAMES = ["C", "C$\\sharp$", "D", "D$\\sharp$", "E", "F",
              "F$\\sharp$", "G", "G$\\sharp$", "A", "A$\\sharp$", "B"]

# Reference Bach means (sanity check), alpha_1..alpha_6 per voice.
REF_BACH = {
    "Bass": [0.130, 0.207, 0.257, 0.118, 0.535, 0.079],
    "Tenor": [0.279, 0.181, 0.261, 0.186, 0.525, 0.190],
    "Alto": [0.363, 0.233, 0.298, 0.197, 0.505, 0.223],
    "Soprano": [0.297, 0.170, 0.233, 0.183, 0.580, 0.216],
}


# --------------------------------------------------------------------------- #
# DATA: recompute the per-voice Fourier characters from the music21 corpora.
# --------------------------------------------------------------------------- #
def pcv(part):
    """Duration-weighted pitch-class vector (12-dim) of a part."""
    v = np.zeros(12)
    for n in part.recurse().notes:
        for p in (n.pitches if n.isChord else [n.pitch]):
            v[p.pitchClass] += float(n.quarterLength) or 0.25
    return v


def coeffs(v):
    """Complex normalized Fourier coefficients c_k = a_k/a_0, k=1..6."""
    a0 = v.sum()
    if a0 <= 0:
        return None
    return np.array(
        [sum(v[x] * np.exp(-2j * np.pi * k * x / 12) for x in range(12)) / a0
         for k in range(1, 7)]
    )


def meanpitch(part):
    ps = [p.midi
          for n in part.recurse().notes
          for p in (n.pitches if n.isChord else [n.pitch])]
    return np.mean(ps) if ps else None


def voice_stats_from_scores(scores, label):
    """Keep 4-part works, rank voices by register (0=bass..3=soprano).
    Return dict with mean |alpha| [4x6], mean complex coeff [4x6], mean
    normalized pcv [4x12], and n_used."""
    alpha = {r: [] for r in range(4)}
    cplx = {r: [] for r in range(4)}
    dist = {r: [] for r in range(4)}
    n_used = n_tot = 0
    for ch in scores:
        n_tot += 1
        try:
            parts = [p for p in ch.parts if any(True for _ in p.recurse().notes)]
            mp = [(meanpitch(p), p) for p in parts]
            mp = [(m, p) for m, p in mp if m is not None]
            if len(mp) != 4:
                continue
            mp.sort(key=lambda t: t[0])  # lowest first = bass
            vs = [pcv(p) for _, p in mp]
            cs = [coeffs(v) for v in vs]
            if any(c is None for c in cs):
                continue
            for r in range(4):
                alpha[r].append(np.abs(cs[r]))
                cplx[r].append(cs[r])
                dist[r].append(vs[r] / vs[r].sum())
            n_used += 1
        except Exception:
            continue
    out = {
        "alpha": np.array([np.array(alpha[r]).mean(0) for r in range(4)]),
        "cplx": np.array([np.array(cplx[r]).mean(0) for r in range(4)]),
        "dist": np.array([np.array(dist[r]).mean(0) for r in range(4)]),
        "n": n_used,
    }
    print(f"  [{label}] 4-part works used: {n_used} (of {n_tot} scanned)")
    return out


def compute_corpus():
    from music21 import corpus

    print("Computing Bach 4-part chorales ...")
    bach = voice_stats_from_scores(
        corpus.chorales.Iterator(numberingSystem="bwv"), "Bach")

    print("Computing Palestrina ...")
    pal_paths = corpus.search("palestrina")

    def pal_iter():
        for md in pal_paths:
            try:
                yield md.parse()
            except Exception:
                continue

    pal = voice_stats_from_scores(pal_iter(), "Palestrina")
    return bach, pal


def phase_of(c_k):
    """Amiot phase  Phi_k = (-6/pi) * arg(a_k)  mod 12  (in pc-units)."""
    return (-6.0 / np.pi) * np.angle(c_k) % 12.0


# --------------------------------------------------------------------------- #
# FIG 1: per-voice camembert (squared-character pie), Bach row + Palestrina row.
# --------------------------------------------------------------------------- #
def fig_camembert(bach, pal, fname):
    fig, axes = plt.subplots(2, 4, figsize=(13.5, 7.4), constrained_layout=True)
    rows = [("J. S. Bach\n(4-part chorales)", bach["alpha"]),
            ("Palestrina", pal["alpha"])]
    wedges = None
    for ri, (rlabel, data) in enumerate(rows):
        for vi in range(4):
            ax = axes[ri, vi]
            weights = np.array(data[vi]) ** 2  # Parseval weighting
            wedges, _ = ax.pie(
                weights, colors=CHAR_COLORS, startangle=90, counterclock=False,
                wedgeprops=dict(edgecolor="white", linewidth=1.3),
                radius=1.18)
            ax.set_aspect("equal")
            if ri == 0:
                ax.set_title(VOICE_NAMES[vi], fontsize=15, fontweight="bold", pad=6)
        axes[ri, 0].set_ylabel(rlabel, fontsize=13, fontweight="bold",
                               rotation=90, labelpad=12)
    fig.legend(wedges, CHAR_NAMES, loc="outside lower center", ncol=6,
               frameon=False, fontsize=11)
    fig.suptitle(
        r"Per-voice Fourier camembert — relative weight of each character $|a_k|^2$",
        fontsize=15.5, fontweight="bold")
    save(fig, fname)


# --------------------------------------------------------------------------- #
# FIG 2: Fourier profile, alpha_k vs k, one line per voice (Bach).
# --------------------------------------------------------------------------- #
def fig_profile(bach, fname):
    fig, ax = plt.subplots(figsize=(8.4, 5.6), constrained_layout=True)
    ks = np.arange(1, 7)
    a = bach["alpha"]
    for vi in range(4):
        ax.plot(ks, a[vi], marker=VOICE_MARKERS[vi], markersize=8, linewidth=2.2,
                color=VOICE_COLORS[vi], label=VOICE_NAMES[vi],
                markeredgecolor="white", markeredgewidth=0.7)
    ax.set_xlabel(r"Fourier index $k$")
    ax.set_ylabel(r"mean character $\alpha_k = |a_k|/|a_0|$")
    ax.set_title("Fourier profile of the four voices  (Bach 4-part chorales)",
                 fontweight="bold")
    ax.set_xticks(ks)
    ax.set_xticklabels(["1\nchrom.", "2\nquartal", "3\naug.", "4\noct.",
                        "5\ndiatonic", "6\nwhole-t."])
    ax.grid(True, alpha=0.3, linestyle=":")
    ax.legend(frameon=True, framealpha=0.95, edgecolor="0.8")
    ax.set_ylim(0, max(0.62, a.max() * 1.12))
    save(fig, fname)


# --------------------------------------------------------------------------- #
# FIG 3: clock diagram — vectors e^{-2 pi i k x/12} summed for a chord, k=5.
# --------------------------------------------------------------------------- #
def fig_clock(fname, chord=(0, 4, 7), k=5):
    fig, ax = plt.subplots(figsize=(7.4, 7.2), constrained_layout=True)
    theta = np.linspace(0, 2 * np.pi, 400)
    ax.plot(np.cos(theta), np.sin(theta), color="0.72", lw=1.3)
    for x in range(12):
        ang = np.pi / 2 - 2 * np.pi * x / 12
        cx, cy = np.cos(ang), np.sin(ang)
        inchord = x in chord
        ax.plot([cx], [cy], "o", ms=13 if inchord else 7,
                color="#d6322c" if inchord else "0.6", zorder=5)
        ax.text(1.17 * cx, 1.17 * cy, NOTE_NAMES[x], ha="center", va="center",
                fontsize=12, fontweight="bold" if inchord else "normal",
                color="#d6322c" if inchord else "0.45")
    vecs = [np.exp(-2j * np.pi * k * x / 12) for x in chord]
    running = 0 + 0j
    col = CHAR_COLORS[k - 1]
    for i, vz in enumerate(vecs):
        start, running = running, running + vz
        ax.add_patch(FancyArrowPatch((start.real, start.imag),
                     (running.real, running.imag), arrowstyle="-|>",
                     mutation_scale=16, lw=2.0, color=col, alpha=0.9, zorder=6))
        mid = (start + running) / 2
        perp = 0.10 * np.exp(1j * (np.angle(vz) + np.pi / 2))
        ax.text(mid.real + perp.real, mid.imag + perp.imag,
                f"pc {chord[i]}", fontsize=10, color=col, ha="center", va="center")
    ax.add_patch(FancyArrowPatch((0, 0), (running.real, running.imag),
                 arrowstyle="-|>", mutation_scale=22, lw=3.0, color="black", zorder=7))
    ax.text(running.real + 0.08, running.imag + 0.05, rf"$a_{{{k}}}$",
            fontsize=16, fontweight="bold", ha="left", va="center")
    ax.text(1.55, -1.05,
            rf"$a_{{{k}}} = \sum_{{x \in \mathrm{{chord}}}} e^{{-2\pi i\,{k}x/12}}$",
            fontsize=13, ha="center", va="center")
    mag = abs(running)
    ax.set_title(
        rf"Clock computation of $a_{{{k}}}$ for the C-major triad $\{{{','.join(map(str,chord))}\}}$"
        + "\n"
        + rf"$|a_{{{k}}}| = {mag:.3f}$  (the diatonic character)",
        fontweight="bold")
    ax.set_xlim(-1.45, 2.6)
    ax.set_ylim(-1.45, 1.45)
    ax.set_aspect("equal")
    ax.axis("off")
    save(fig, fname)


# --------------------------------------------------------------------------- #
# FIG 4: phase torus surface, like Amiot's Fig.18.
# --------------------------------------------------------------------------- #
def fig_torus(fname):
    fig = plt.figure(figsize=(7.6, 6.3), constrained_layout=True)
    ax = fig.add_subplot(111, projection="3d")
    R, r = 2.0, 0.85
    u = np.linspace(0, 2 * np.pi, 90)
    v = np.linspace(0, 2 * np.pi, 90)
    U, V = np.meshgrid(u, v)
    X = (R + r * np.cos(V)) * np.cos(U)
    Y = (R + r * np.cos(V)) * np.sin(U)
    Z = r * np.sin(V)
    C = np.cos(3 * U) + np.cos(5 * V)
    ax.plot_surface(X, Y, Z,
                    facecolors=plt.cm.twilight((C - C.min()) / (np.ptp(C) + 1e-9)),
                    rstride=1, cstride=1, linewidth=0, antialiased=True, shade=False)
    ax.set_title(r"Phase torus  (phase of $a_3$ vs phase of $a_5$)", fontweight="bold")
    ax.set_xlabel(r"phase $a_3$")
    ax.set_ylabel(r"phase $a_5$")
    ax.set_zticks([])
    ax.view_init(elev=34, azim=-52)
    ax.set_box_aspect((1, 1, 0.45))
    save(fig, fname)


# --------------------------------------------------------------------------- #
# FIG 5: per-voice duration-weighted pitch-class distribution on the 12-clock.
# --------------------------------------------------------------------------- #
def fig_pc_clock(bach, fname):
    dist = bach["dist"]
    rmax = dist.max()
    fig, axes = plt.subplots(1, 4, figsize=(15.5, 4.7),
                             subplot_kw=dict(projection="polar"),
                             constrained_layout=True)
    width = 2 * np.pi / 12 * 0.86
    for vi in range(4):
        ax = axes[vi]
        ax.set_theta_zero_location("N")
        ax.set_theta_direction(-1)
        thetas = 2 * np.pi * np.arange(12) / 12
        heights = dist[vi]
        ax.bar(thetas, heights, width=width, bottom=0.0,
               color=VOICE_COLORS[vi], edgecolor="white", linewidth=0.8, alpha=0.92)
        ax.set_ylim(0, rmax * 1.05)
        ax.set_xticks(thetas)
        ax.set_xticklabels(NOTE_NAMES, fontsize=10)
        ax.set_yticklabels([])
        ax.grid(alpha=0.25)
        ax.set_title(rf"{VOICE_NAMES[vi]}   ($\alpha_1$={bach['alpha'][vi,0]:.2f})",
                     fontsize=13, fontweight="bold", pad=14)
    fig.suptitle(
        "Per-voice pitch-class distribution on the 12-note clock  (Bach 4-part chorales)\n"
        r"spread weight $\Rightarrow$ low $\alpha_1$ (bass);  clustered weight $\Rightarrow$ high $\alpha_1$ (alto)",
        fontsize=14, fontweight="bold")
    save(fig, fname)


# --------------------------------------------------------------------------- #
# FIG 6: flat phase plane (Phi_3, Phi_5), per-voice mean point + triad lattice.
# --------------------------------------------------------------------------- #
def fig_phase_plane(bach, fname):
    fig, ax = plt.subplots(figsize=(7.6, 7.2), constrained_layout=True)
    # reference: 12 major + 12 minor triads
    maj, minr = [], []
    for t in range(12):
        for tri, store in (((t, (t + 4) % 12, (t + 7) % 12), maj),
                           ((t, (t + 3) % 12, (t + 7) % 12), minr)):
            v = np.zeros(12)
            for x in tri:
                v[x] = 1.0
            c = coeffs(v)
            store.append((phase_of(c[2]), phase_of(c[4])))  # (Phi3, Phi5)
    maj = np.array(maj)
    minr = np.array(minr)
    ax.scatter(maj[:, 0], maj[:, 1], s=55, marker="^", facecolor="none",
               edgecolor="0.55", linewidth=1.1, label="major triads", zorder=3)
    ax.scatter(minr[:, 0], minr[:, 1], s=55, marker="v", facecolor="none",
               edgecolor="0.75", linewidth=1.1, label="minor triads", zorder=3)
    # per-voice mean phase points (genuinely clustered -> separate them in an inset)
    vpts = []
    for vi in range(4):
        c = bach["cplx"][vi]
        p3, p5 = phase_of(c[2]), phase_of(c[4])
        vpts.append((p3, p5))
        ax.scatter([p3], [p5], s=240, marker=VOICE_MARKERS[vi],
                   color=VOICE_COLORS[vi], edgecolor="white", linewidth=1.5,
                   zorder=6, label=VOICE_NAMES[vi])
    vpts = np.array(vpts)
    # zoomed inset showing the four near-coincident voice points resolved
    cx, cy = vpts[:, 0].mean(), vpts[:, 1].mean()
    pad = 0.7
    axin = ax.inset_axes([0.05, 0.05, 0.34, 0.34])
    in_off = [(8, 5), (8, 6), (6, -16), (8, 6)]  # Bass, Tenor, Alto, Soprano
    for vi in range(4):
        p3, p5 = vpts[vi]
        axin.scatter([p3], [p5], s=160, marker=VOICE_MARKERS[vi],
                     color=VOICE_COLORS[vi], edgecolor="white", linewidth=1.3,
                     zorder=6)
        axin.annotate(VOICE_NAMES[vi], (p3, p5), textcoords="offset points",
                      xytext=in_off[vi], fontsize=9.5, fontweight="bold",
                      color=VOICE_COLORS[vi])
    axin.set_xlim(cx - pad, cx + pad)
    axin.set_ylim(cy - pad, cy + pad)
    axin.set_title("zoom on voices", fontsize=9)
    axin.tick_params(labelsize=8)
    axin.grid(True, alpha=0.3, linestyle=":")
    ax.indicate_inset_zoom(axin, edgecolor="0.4")
    ax.set_xlim(0, 12)
    ax.set_ylim(0, 12)
    ax.set_xticks(range(0, 13, 2))
    ax.set_yticks(range(0, 13, 2))
    ax.set_xlabel(r"phase $\Phi_3$  (augmented axis)")
    ax.set_ylabel(r"phase $\Phi_5$  (diatonic / circle-of-fifths axis)")
    ax.set_aspect("equal")
    ax.grid(True, alpha=0.3, linestyle=":")
    ax.set_title(r"Phase plane $(\Phi_3,\Phi_5)$ of the four voices"
                 + "\n" + r"$\Phi_k = -\frac{6}{\pi}\arg(a_k)\ \mathrm{mod}\ 12$"
                 + "   (Bach 4-part chorales)", fontweight="bold")
    ax.legend(loc="upper right", framealpha=0.95, edgecolor="0.8", fontsize=10)
    save(fig, fname)


# --------------------------------------------------------------------------- #
# FIG 7: signature heatmap (voices x characters), Bach + Palestrina panels.
# --------------------------------------------------------------------------- #
def fig_heatmap(bach, pal, fname):
    fig, axes = plt.subplots(1, 2, figsize=(13.5, 4.6), constrained_layout=True)
    data = [("J. S. Bach", bach["alpha"]), ("Palestrina", pal["alpha"])]
    vmax = max(bach["alpha"].max(), pal["alpha"].max())
    col_labels = [r"$a_1$" + "\nchrom.", r"$a_2$" + "\nquartal", r"$a_3$" + "\naug.",
                  r"$a_4$" + "\noct.", r"$a_5$" + "\ndiatonic", r"$a_6$" + "\nwhole-t."]
    im = None
    for pi, (title, M) in enumerate(data):
        ax = axes[pi]
        im = ax.imshow(M, cmap="viridis", vmin=0, vmax=vmax, aspect="auto")
        ax.set_xticks(range(6))
        ax.set_xticklabels(col_labels, fontsize=10)
        ax.set_yticks(range(4))
        ax.set_yticklabels(VOICE_NAMES, fontsize=11)
        ax.set_title(title, fontweight="bold", fontsize=14)
        for r in range(4):
            for c in range(6):
                val = M[r, c]
                ax.text(c, r, f"{val:.3f}", ha="center", va="center",
                        fontsize=10.5,
                        color="white" if val < vmax * 0.55 else "black")
        ax.set_xticks(np.arange(-.5, 6, 1), minor=True)
        ax.set_yticks(np.arange(-.5, 4, 1), minor=True)
        ax.grid(which="minor", color="white", linewidth=1.2)
        ax.tick_params(which="minor", length=0)
    cb = fig.colorbar(im, ax=axes, fraction=0.025, pad=0.02)
    cb.set_label(r"mean character $\alpha_k = |a_k|/|a_0|$", fontsize=11)
    fig.suptitle("Per-voice Fourier signature (character magnitudes)",
                 fontsize=15, fontweight="bold")
    save(fig, fname)


# --------------------------------------------------------------------------- #
# FIG 8: Dirichlet kernel sin(d x)/sin(x), d=7 (generated-scale coefficient).
# --------------------------------------------------------------------------- #
def fig_dirichlet(fname, d=7):
    fig, ax = plt.subplots(figsize=(8.4, 5.2), constrained_layout=True)
    x = np.linspace(-np.pi, np.pi, 2000)
    x = x[np.abs(np.sin(x)) > 1e-6]
    y = np.sin(d * x) / np.sin(x)
    ax.plot(x, y, color=CHAR_COLORS[4], lw=2.2)
    ax.axhline(0, color="0.6", lw=0.8)
    ax.axvline(0, color="0.6", lw=0.8)
    # mark the integer-lattice sample points k*pi/12 (DFT bins)
    ks = np.arange(-6, 7)
    xs = ks * np.pi / 12
    xs = xs[np.abs(np.sin(xs)) > 1e-6]
    ax.plot(xs, np.sin(d * xs) / np.sin(xs), "o", color="black", ms=6, zorder=5,
            label=r"DFT bins $k\pi/12$")
    ax.set_xlabel(r"$\theta$")
    ax.set_ylabel(r"$\dfrac{\sin(d\,\theta)}{\sin(\theta)}$")
    ax.set_title(rf"Dirichlet kernel ($d={d}$): magnitude of a generated-scale coefficient",
                 fontweight="bold")
    ax.set_xticks([-np.pi, -np.pi/2, 0, np.pi/2, np.pi])
    ax.set_xticklabels([r"$-\pi$", r"$-\pi/2$", "0", r"$\pi/2$", r"$\pi$"])
    ax.grid(True, alpha=0.3, linestyle=":")
    ax.legend(framealpha=0.95, edgecolor="0.8")
    save(fig, fname)


# --------------------------------------------------------------------------- #
def save(fig, fname):
    png = os.path.join(HERE, fname + ".png")
    pdf = os.path.join(HERE, fname + ".pdf")
    fig.savefig(png)
    fig.savefig(pdf)
    plt.close(fig)
    print(f"  saved {png}")
    print(f"  saved {pdf}")


def sanity_check(bach):
    print("\nSanity check vs reference Bach means (max abs diff per voice):")
    for vi, name in enumerate(VOICE_NAMES):
        ref = np.array(REF_BACH[name])
        got = np.array(bach["alpha"][vi])
        print(f"  {name:8s} maxdiff={np.abs(ref - got).max():.4f}   "
              + " ".join(f"{x:.3f}" for x in got))


def main():
    bach, pal = compute_corpus()
    sanity_check(bach)
    print("\nRendering figures ...")
    fig_camembert(bach, pal, "fig1_camembert")
    fig_profile(bach, "fig2_fourier_profile")
    fig_clock("fig3_clock_a5")
    fig_torus("fig4_phase_torus")
    fig_pc_clock(bach, "fig5_pc_clock")
    fig_phase_plane(bach, "fig6_phase_plane")
    fig_heatmap(bach, pal, "fig7_heatmap")
    fig_dirichlet("fig8_dirichlet")
    print("\nDone.")


if __name__ == "__main__":
    main()
