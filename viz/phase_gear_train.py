#!/usr/bin/env python3
# phase_gear_train.py — the rotation speeds of the Fourier "tori" under transposition:
# a gear train of speeds 0..6 that re-synchronises at the octave.
# Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as AI assistant)
#
# THE DYNAMICS. Transposition T_t multiplies the k-th Fourier coefficient by e^{-2*pi*i*k*t/12}:
#   a_k(T_t A) = e^{-2*pi*i*k*t/12} * a_k(A).
# So coordinate k ROTATES AT SPEED k. Over the 12 transpositions t=0..11 its phasor visits
#   12 / gcd(k,12) distinct positions -- the gear has that many teeth -- and ALL gears realign at
#   t=12 (the octave). The radius is |a_k|, the triad's Fourier balance. Standard Quinn-Amiot quality
#   dictionary (fixed by which scale maximizes each |a_k|): |a_0|=card, |a_1|=chromatic,
#   |a_3|=AUGMENTED, |a_4|=OCTATONIC/dim, |a_5|=diatonic, |a_6|=WHOLE-TONE. (a_6 is the tritone
#   FREQUENCY but the quality it detects is whole-tone.)
#
# k=0: speed 0, 1 position  -> DOES NOT MOVE (the fixed hub = cardinality).
# k=6: speed 6, 2 positions -> the tritone frequency, real, just flips sign (period 2).
# teeth = 12/gcd(k,12): k=4 -> 3; k=3 -> 4; k=2 -> 6; k=6 -> 2; k=1,5 -> 12.
#
# Output: viz/out/phase_gear_train.png

import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

A = [0, 4, 7]   # C major triad (set class 3-11) -- the Tonnetz generator

def a_k(k):
    return sum(np.exp(-2j * np.pi * k * n / 12) for n in A)

from math import gcd
QUAL = {0: "card (DC)", 1: "chromatic", 2: "(period 6)", 3: "augmented",
        4: "octatonic/dim", 5: "diatonic/5ths", 6: "whole-tone"}

fig, axes = plt.subplots(1, 7, figsize=(17, 3.0))
for k, ax in enumerate(axes):
    ak = a_k(k)
    mag = abs(ak)
    teeth = 12 // gcd(k, 12) if k > 0 else 1
    # unit guide circle
    th = np.linspace(0, 2 * np.pi, 200)
    ax.plot(np.cos(th), np.sin(th), color="0.85", lw=0.8)
    # the orbit of a_k under the 12 transpositions (radius = |a_k|, normalised to <=1 for display)
    rad = 0.15 + 0.8 * (mag / 3.0)   # 3 = max (|a_0|); shows the balance magnitude
    pts = []
    for t in range(12):
        z = ak * np.exp(-2j * np.pi * k * t / 12)
        ph = np.angle(z)
        pts.append((rad * np.cos(ph), rad * np.sin(ph)))
    pts = np.array(pts)
    # distinct positions (the gear teeth)
    uniq = np.unique(np.round(pts, 3), axis=0)
    # draw the speed arrow (from center) at t=0
    z0 = ak if mag > 1e-9 else 1.0
    ph0 = np.angle(z0)
    col = "#1B6F8C" if k in (3, 4) else ("#B5530F" if k == 6 else "0.25")
    ax.annotate("", xy=(rad * np.cos(ph0), rad * np.sin(ph0)), xytext=(0, 0),
                arrowprops=dict(arrowstyle="-|>", color=col, lw=1.6))
    ax.scatter(uniq[:, 0], uniq[:, 1], color=col, s=24, zorder=5)
    ax.scatter([0], [0], color="black", s=12, zorder=6)
    spd = "0 (still)" if k == 0 else f"{k}"
    ax.set_title(f"$a_{{{k}}}$  speed {spd}\n{teeth} pos · |a|={mag:.2f}\n{QUAL[k]}", fontsize=8.5)
    ax.set_xlim(-1.1, 1.1); ax.set_ylim(-1.1, 1.1); ax.set_aspect("equal"); ax.axis("off")

fig.suptitle("Transposition as a gear train: coordinate $a_k$ rotates at speed $k$, visiting "
             "$12/\\gcd(k,12)$ positions; all re-synchronise at the octave $t=12$.  "
             "(C major triad; radius $=|a_k|$ = the Fourier balance)", fontsize=11)
out_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
os.makedirs(out_dir, exist_ok=True)
out_path = os.path.join(out_dir, "phase_gear_train.png")
fig.tight_layout(rect=(0, 0, 1, 0.86))
fig.savefig(out_path, dpi=140, bbox_inches="tight")
print(f"wrote {out_path}")
for k in range(7):
    print(f"  a_{k}: speed {k}, {12//gcd(k,12) if k>0 else 1} distinct positions, "
          f"period {12//gcd(k,12) if k>0 else 1}, |a_k|={abs(a_k(k)):.3f}  [{QUAL[k]}]")
