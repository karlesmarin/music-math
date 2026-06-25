#!/usr/bin/env python3
# solenoid_dyadic.py — the Smale-Williams solenoid: a torus inside a torus, wrapping twice, iterated;
# the genuine fractal anchored to the CRT torus's diminished (Z4) factor = the 2-adic octave tower.
# Author: Carles Marin <karlesmarin@gmail.com>  (with Claude, Anthropic, as AI assistant)
#
# THE OBJECT. The Smale-Williams solenoid is the nested intersection of solid tori T_0 > T_1 > T_2 > ...
# where T_{n+1} sits inside T_n wrapping around its longitude TWICE, at half the tube radius. Its core
# curve C_n winds 2^n times around the big circle; the limit is a fractal, locally Cantor-set x arc.
# It is the INVERSE LIMIT of the circle under the doubling map z |-> z^2.
#
# THE MUSIC (anchor to the CRT torus Z12 = Z3 x Z4). The Z4 factor is the DIMINISHED-7th cycle
# {0,3,6,9} -- the 2-part of the chromatic, level n=2 of the dyadic tower
#     Z2 = {0,6} (tritone)  <  Z4 = {0,3,6,9} (dim7)  <  Z8  <  ...  <  Z_{2^n}  <  ...
# = halving the octave again and again (2-EDO < 4-EDO < 8-EDO < ...). Each doubling is one wrap of the
# solenoid; the inverse limit (all dyadic equal temperaments at once) is the 2-adic solenoid. The tritone
# 2^{n-1} is the 2-torsion at EVERY level (our `tritone_selfPaired` iterated), and the FFT/DFT block
# decomposition refines self-similarly up the tower (Cooley-Tukey). The solenoid is classic math
# (Vietoris-van Dantzig; Smale-Williams attractor); the dyadic-octave anchoring is the framing.
#
# Output: viz/out/solenoid_dyadic.png

import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401

R = 2.4  # big-circle radius

fig = plt.figure(figsize=(11, 9))
ax = fig.add_subplot(111, projection="3d")

# --- ambient torus T_0 (light context) ---
r0 = 0.85
u = np.linspace(0, 2 * np.pi, 70); v = np.linspace(0, 2 * np.pi, 30)
U, V = np.meshgrid(u, v)
ax.plot_surface((R + r0 * np.cos(V)) * np.cos(U), (R + r0 * np.cos(V)) * np.sin(U),
                r0 * np.sin(V), color="0.9", alpha=0.10, linewidth=0)

# --- the solenoid approximants C_n: core winds 2^n times around the longitude, tube radius -> 0 ---
levels = [0, 1, 2, 3]
cols = ["#1B6F8C", "#3E8FA6", "#C9772F", "#B5530F"]
labs = ["$C_0$: core = dim7 cycle $\\mathbb{Z}_4$ (1 wrap, 4-EDO)",
        "$C_1$: 2 wraps (8-EDO)", "$C_2$: 4 wraps (16-EDO)", "$C_3$: 8 wraps (32-EDO)"]
for n, col, lab in zip(levels, cols, labs):
    a = 0.62 / (1.7 ** n)                     # shrinking tube radius
    theta = np.linspace(0, 2 * np.pi, 60 * 2 ** n + 400)
    lon = (2 ** n) * theta                    # winds 2^n times around the big circle
    off = a * np.cos(theta)                   # in-tube offset rotates once -> consecutive passes nest
    X = (R + off) * np.cos(lon)
    Y = (R + off) * np.sin(lon)
    Z = a * np.sin(theta)
    ax.plot(X, Y, Z, color=col, lw=1.3 if n < 2 else 0.8, alpha=0.9, label=lab)

# --- the four diminished-7th nodes {0,3,6,9} on the core circle (level Z4), tritone {0,6} marked ---
for pc in (0, 3, 6, 9):
    ang = 2 * np.pi * pc / 12.0
    p = np.array([R * np.cos(ang), R * np.sin(ang), 0.0])
    ax.scatter(*p, color="black", s=45, zorder=10)
    ax.text(p[0] * 1.06, p[1] * 1.06, p[2] + 0.15, str(pc), fontsize=9, zorder=11)
# tritone pair 0-6 = the Z2 level
ang0, ang6 = 0.0, np.pi
ax.plot([R, -R], [0, 0], [0, 0], color="black", lw=1.0, ls=":", alpha=0.6)

ax.set_title("The Smale-Williams solenoid: a torus inside a torus, wrapping twice, iterated\n"
             "core = the diminished $\\mathbb{Z}_4$ cycle; doubling = halving the octave "
             "($\\mathbb{Z}_4\\!\\subset\\!\\mathbb{Z}_8\\!\\subset\\!\\cdots$) "
             "= the 2-adic tower; the limit is fractal (Cantor $\\times$ arc)", fontsize=10.5)
ax.legend(loc="upper left", fontsize=8, framealpha=0.9)
ax.set_box_aspect((1, 1, 0.45)); ax.set_axis_off(); ax.view_init(elev=42, azim=-60)

out_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
os.makedirs(out_dir, exist_ok=True)
out_path = os.path.join(out_dir, "solenoid_dyadic.png")
fig.savefig(out_path, dpi=150, bbox_inches="tight")
print(f"wrote {out_path}")
print("dyadic tower: Z2={0,6} (tritone) < Z4={0,3,6,9} (dim7) < Z8 < ... -> 2-adic solenoid")
print("tritone 2^(n-1) = the 2-torsion at every level (tritone_selfPaired iterated)")
