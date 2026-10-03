"""Publication figure from the exact, independently checked seven-note census."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import argparse
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from math import sqrt

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from huddling_verify import interval_vector, m5, ps_coordinates, verify

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output-dir", type=Path, default=ROOT / "paper" / "figs")
parser.add_argument("--language", choices=["en", "es"], default="en")
args = parser.parse_args()
spanish = args.language == "es"

verify()
points = Counter()
for a in combinations(range(12), 7):
    p, q = ps_coordinates(m5(a))
    energy = sum(v*(6-j)**2 for j, v in enumerate(interval_vector(a)))
    points[(p, q, energy)] += 1

plt.rcParams.update({"font.family": "serif", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42})
fig, ax = plt.subplots(figsize=(6.3, 3.6), layout="constrained")
ordinary = [(p, q, e, n) for (p, q, e), n in points.items() if e != 313]
ax.scatter([(p+q*sqrt(3))/2 for p, q, e, n in ordinary],
           [e for p, q, e, n in ordinary],
           s=[8+1.5*n for p, q, e, n in ordinary],
           facecolor="#1B6F8C", edgecolor="white", linewidth=.35, alpha=.65)
peak = 7 + 4*sqrt(3)
ax.scatter([peak], [313], s=80, marker="D", color="#B5530F", zorder=4)
annotation = ("Órbita diatónica: 12 conjuntos\npotencia máxima, energía mínima" if spanish else
              "Diatonic orbit: 12 sets\nmaximum power, minimum energy")
ax.annotate(annotation,
            xy=(peak, 313), xytext=(7.4, 358),
            arrowprops={"arrowstyle": "->", "color": "#B5530F"},
            ha="left", va="center", fontsize=9)
ax.axhline(313, color="#B5530F", linestyle=":", linewidth=.8, alpha=.65)
ax.set_xlabel((r"Potencia de Fourier en frecuencia cinco $|\widehat A(5)|^2$" if spanish else
               r"Fifth Fourier power $|\widehat A(5)|^2$"))
ax.set_ylabel((r"Energía de todos los pares $E_{V_0}(A)$, $V_0(k)=(7-k)^2$" if spanish else
               r"All-pairs energy $E_{V_0}(A)$, $V_0(k)=(7-k)^2$"))
ax.set_xlim(-.4, 14.6)
ax.set_ylim(303, max(e for p, q, e in points)+10)
ax.grid(axis="y", alpha=.15)
destination = args.output_dir
destination.mkdir(parents=True, exist_ok=True)
stem = "huddling_energy_es" if spanish else "huddling_energy"
fig.savefig(destination / (stem + ".pdf"))
fig.savefig(destination / (stem + ".png"), dpi=180)
print(f"792 sets, {len(points)} exact (power, energy) classes; diatonic multiplicity {points[(14, 8, 313)]}.")
