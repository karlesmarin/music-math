#!/usr/bin/env python3
# torus_two_level.py — the chromatic universe Z12 as a DIAGONAL winding on the CRT torus
# Z3 x Z4, with its two levels of synchronization.
# Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as AI assistant)
#
# WHAT IT SHOWS. By the Chinese Remainder Theorem Z12 ~= Z3 x Z4, so each pitch class
# x maps to (x mod 3, x mod 4) -- a point on a torus T^2 whose two circle-directions are:
#   * theta1 (the Z3 factor)  = the AUGMENTED-triad / whole-tone axis  (what a_4 detects),
#   * theta2 (the Z4 factor)  = the DIMINISHED-seventh / octatonic axis (what a_3 detects).
# TWO LEVELS OF SYNCHRONIZATION:
#   Level 1 (internal, locked): each factor circle rotates rigidly -- an augmented triad
#           {0,4,8} is a theta1-circle at fixed theta2; a diminished seventh {0,3,6,9} is a
#           theta2-circle at fixed theta1. Rotate one factor = one "sense".
#   Level 2 (global, coupled): transposition by a semitone is the DIAGONAL step (+1,+1),
#           coupling both factors into one clock -- the chromatic circle is the (1,1) winding
#           that visits all 12 lattice points and closes after 12 steps (lcm(3,4)=12).
#
# Output: viz/out/torus_two_level.png

import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401

R, r = 2.0, 0.85  # major / minor radii

def torus_xyz(t1, t2):
    """(theta1, theta2) -> 3D point on the torus."""
    x = (R + r * np.cos(t2)) * np.cos(t1)
    y = (R + r * np.cos(t2)) * np.sin(t1)
    z = r * np.sin(t2)
    return np.array([x, y, z])

def pc_angles(x):
    """pitch class x -> (theta1, theta2) via CRT (x mod 3, x mod 4)."""
    return (2 * np.pi * (x % 3) / 3.0, 2 * np.pi * (x % 4) / 4.0)

fig = plt.figure(figsize=(11, 8))
ax = fig.add_subplot(111, projection="3d")

# --- the torus surface (light context) ---
u = np.linspace(0, 2 * np.pi, 80)
v = np.linspace(0, 2 * np.pi, 40)
u, v = np.meshgrid(u, v)
Xs = (R + r * np.cos(v)) * np.cos(u)
Ys = (R + r * np.cos(v)) * np.sin(u)
Zs = r * np.sin(v)
ax.plot_surface(Xs, Ys, Zs, color="0.9", alpha=0.18, linewidth=0, antialiased=True, zorder=0)

# --- LEVEL 2: the chromatic diagonal winding 0->1->...->11->0 (smooth) ---
ts = np.linspace(0, 12, 600)
diag = np.array([torus_xyz(2 * np.pi * t / 3.0, 2 * np.pi * t / 4.0) for t in ts])
ax.plot(diag[:, 0], diag[:, 1], diag[:, 2], color="0.35", lw=1.6, zorder=2,
        label="chromatic = diagonal (1,1)  [level 2: coupled]")

# --- LEVEL 1, factor A: the augmented-triad theta1-circle {0,4,8} (fixed theta2=0) ---
t1c = np.linspace(0, 2 * np.pi, 200)
augc = np.array([torus_xyz(a, 0.0) for a in t1c])
ax.plot(augc[:, 0], augc[:, 1], augc[:, 2], color="#1B6F8C", lw=3.0, zorder=3,
        label=r"augmented axis $\theta_1$ ($a_4$)  [level 1: locked]")

# --- LEVEL 1, factor B: the diminished-7th theta2-circle {0,3,6,9} (fixed theta1=0) ---
t2c = np.linspace(0, 2 * np.pi, 200)
dimc = np.array([torus_xyz(0.0, b) for b in t2c])
ax.plot(dimc[:, 0], dimc[:, 1], dimc[:, 2], color="#B5530F", lw=3.0, zorder=3,
        label=r"diminished axis $\theta_2$ ($a_3$)  [level 1: locked]")

# --- the 12 pitch classes as labelled points ---
NAMES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
for x in range(12):
    t1, t2 = pc_angles(x)
    p = torus_xyz(t1, t2)
    ax.scatter(*p, color="black", s=38, zorder=5)
    q = torus_xyz(t1, t2 + 0.0) * 1.0
    # nudge label outward
    out = torus_xyz(t1, t2)
    n = out / np.linalg.norm(out[:2]) if np.linalg.norm(out[:2]) else out
    ax.text(p[0] + 0.12 * np.cos(t1), p[1] + 0.12 * np.sin(t1), p[2] + 0.10,
            f"{x}", fontsize=8, color="black", zorder=6)

ax.set_title("The chromatic universe as a diagonal winding on the CRT torus "
             r"$\mathbb{Z}_{12}\cong\mathbb{Z}_3\times\mathbb{Z}_4$"
             "\nTwo levels of synchronization: factor-locked (1) vs diagonal-coupled (2)",
             fontsize=11)
ax.legend(loc="upper left", fontsize=8, framealpha=0.9)
ax.set_box_aspect((1, 1, 0.5))
ax.set_axis_off()
ax.view_init(elev=32, azim=-58)

out_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
os.makedirs(out_dir, exist_ok=True)
out_path = os.path.join(out_dir, "torus_two_level.png")
fig.tight_layout()
fig.savefig(out_path, dpi=150, bbox_inches="tight")
print(f"wrote {out_path}")

# quick sanity: print the CRT coordinates + verify the two factor cycles
print("pc -> (mod3, mod4):", {x: (x % 3, x % 4) for x in range(12)})
print("augmented {0,4,8} mod4:", {x: x % 4 for x in (0, 4, 8)}, "(should be constant)")
print("dim7 {0,3,6,9} mod3:", {x: x % 3 for x in (0, 3, 6, 9)}, "(should be constant)")
