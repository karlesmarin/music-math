#!/usr/bin/env python3
# make_audio_micro.py - microtonal (24-EDO / quarter-tone) sonification companion for Note #3.
# Author: Carles Marin (with Claude, Anthropic, as AI assistant).
#
# The saturation rule of Appendix A is universe-generic: in Z_N the maximal-|a_k| set of
# cardinality gcd(N,k) is the coset c + H_k, H_k = (N/gcd(N,k))*Z_N. This renders its N=24
# (quarter-tone) instance - the microtonal analogue of Messiaen's modes of limited transposition.
# WAV only: 24-EDO needs no equal-tempered MIDI hack (a quarter tone is not a MIDI semitone), so
# we synthesise the frequencies directly (f0 * 2^(q/24)) with the same additive-sine voice as the
# 12-EDO companion. Each coset H_k is heard as an ascending run, the saturated balance |a_k|=gcd(24,k).
#   microtonal_z24 - H_3 {0,8,16} -> H_4 {0,6,12,18} -> H_6 -> H_8 -> H_12 (whole-tone-24).
# Run:  python make_audio_micro.py    (writes microtonal_z24.wav into this directory)

import wave
from math import gcd
import numpy as np

SR = 44100
F0 = 261.6256          # middle C (C4), the 0 of Z_24

# ---------------- 24-EDO saturating cosets H_k = (N/gcd)*Z_N ----------------
N = 24
def H(k):
    step = N // gcd(N, k)
    return sorted({(step * j) % N for j in range(N)})

COSETS = [(k, H(k)) for k in (3, 4, 6, 8, 12)]   # |a_k| = 3,4,6,8,12 (whole-tone-24)

# ---------------- WAV render (additive sine, matches make_audio.py voice) ----------------
def _freq(q): return F0 * 2.0 ** (q / 24.0)      # q in Z_24 -> quarter-tone frequency
def _tone(q, dur):
    n = int(dur * SR); t = np.arange(n) / SR; f = _freq(q)
    y = np.sin(2*np.pi*f*t) + 0.5*np.sin(2*np.pi*2*f*t) + 0.25*np.sin(2*np.pi*3*f*t)
    a = max(1, int(0.012 * SR)); env = np.ones(n)
    env[:a] = np.linspace(0, 1, a); env[-a:] = np.linspace(1, 0, a)
    return y * env
def _chord(qs, dur):
    s = sum(_tone(q, dur) for q in qs); return s / max(1e-9, np.max(np.abs(s)))

def write_wav(path, events, gap=0.10):
    g = np.zeros(int(gap * SR)); out = []
    for qs, dur in events: out += [_chord(qs, dur), g]
    sig = np.concatenate(out); sig = sig / max(1e-9, np.max(np.abs(sig))) * 0.9
    with wave.open(path, 'w') as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(SR)
        w.writeframes((sig * 32767).astype('<i2').tobytes())
    print("wrote", path)

# each coset: ascending run of its quarter-tones, then the whole coset as a sustained chord.
events = []
for k, Hk in COSETS:
    events += [([q], 0.30) for q in Hk]          # the mode as a quarter-tone run
    events += [(Hk, 1.6)]                          # the saturated balance, sounded together
write_wav("microtonal_z24.wav", events)
print("done: Z_24 saturating cosets", [(k, len(h)) for k, h in COSETS])
