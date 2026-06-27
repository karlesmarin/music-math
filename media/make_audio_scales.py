#!/usr/bin/env python3
# make_audio_scales.py - sonification companion for the CORPUS PAPER, Pillar 3 (scales & tuning).
# Author: Carles Marin (with Claude, Anthropic, as AI assistant).
#
# Each example is the audible form of one Pillar-3 result. 12-EDO examples emit a MIDI file
# (editable) and a self-contained additive-sine WAV; the tuning (comma) examples are microtonal
# and emit WAV only (built from exact frequency ratios, so the comma is literally heard):
#   diatonic_scale       - the maximally even 7-of-12 (the diatonic), ascending (IsMaxEven).
#   pentatonic_scale     - the maximally even 5-of-12 (the pentatonic).
#   even_vs_cluster      - the diatonic (even) vs the 7-note chromatic cluster {0..6} (un-even);
#                          why the all-pairs energy singles out the diatonic (diatonic_unique).
#   circle_of_fifths     - stepping by the reduced fifth (7 semitones) through all 12 pitch
#                          classes and closing (circle_of_fifths_complete).
#   pythagorean_comma    - twelve PURE fifths (3/2) stacked vs seven octaves (2/1): the same note
#                          a Pythagorean comma apart (531441/524288 ~ 23.46 cents), heard as a beat
#                          (closure_defect_eq_pc / ker_v12_eq_span_pc).
#   syntonic_comma       - four pure fifths (81/64) vs a pure major third (5/4): the syntonic comma
#                          81/80 ~ 21.5 cents (meantone_defect_eq_syntonic / four_fifths_eq_major_third).
# Run:  python make_audio_scales.py    (writes .mid + .wav into this directory)

import struct, wave
import numpy as np

SR = 44100

# ---------------- pitch-class helpers (12-EDO) ----------------
def midis(pcs, base=60): return [base + (p % 12) for p in pcs]
diatonic   = [0, 2, 4, 5, 7, 9, 11]        # maximally even 7-of-12 (7-35)
pentatonic = [0, 2, 4, 7, 9]               # maximally even 5-of-12
cluster7   = [0, 1, 2, 3, 4, 5, 6]         # a NON-even 7-set (chromatic cluster)
def asc(pcs, top=True):
    seq = [[p] for p in pcs]
    if top: seq.append([pcs[0]])
    return seq
def fifths_walk():                          # 0,7,2,9,... all twelve pcs by the reduced fifth
    return [[(7 * i) % 12] for i in range(13)]

# ---------------- MIDI writer (pure Python, 12-EDO) ----------------
def _vlq(n):
    out = [n & 0x7f]; n >>= 7
    while n: out.append((n & 0x7f) | 0x80); n >>= 7
    return bytes(reversed(out))
def write_midi(path, events, tpq=480, bpm=100, vel=80, gap_beats=0.12):
    tr = bytearray()
    tr += _vlq(0) + bytes([0xFF, 0x51, 0x03]) + int(60_000_000 / bpm).to_bytes(3, 'big')
    tr += _vlq(0) + bytes([0xC0, 0]); pending = 0
    for pcs, beats in events:
        ns = midis(pcs)
        for i, nt in enumerate(ns):
            tr += _vlq(pending if i == 0 else 0) + bytes([0x90, nt, vel]); pending = 0
        dur = int(beats * tpq)
        for i, nt in enumerate(ns):
            tr += _vlq(dur if i == 0 else 0) + bytes([0x80, nt, 0])
        pending = int(gap_beats * tpq)
    tr += _vlq(0) + bytes([0xFF, 0x2F, 0x00])
    hdr = b'MThd' + struct.pack('>IHHH', 6, 0, 1, tpq)
    with open(path, 'wb') as f: f.write(hdr + b'MTrk' + struct.pack('>I', len(tr)) + bytes(tr))
    print("wrote", path)

# ---------------- WAV render ----------------
def _f_midi(m): return 440.0 * 2.0 ** ((m - 69) / 12.0)
def _tone_f(freq, dur, amp=1.0):
    n = int(dur * SR); t = np.arange(n) / SR
    y = np.sin(2*np.pi*freq*t) + 0.5*np.sin(2*np.pi*2*freq*t) + 0.25*np.sin(2*np.pi*3*freq*t)
    a = max(1, int(0.012 * SR)); env = np.ones(n)
    env[:a] = np.linspace(0, 1, a); env[-a:] = np.linspace(1, 0, a)
    return amp * y * env
def _chord_midi(pcs, dur):
    s = sum(_tone_f(_f_midi(m), dur) for m in midis(pcs)); return s / max(1e-9, np.max(np.abs(s)))
def write_wav_pc(path, events, gap=0.08):
    g = np.zeros(int(gap * SR)); out = []
    for pcs, dur in events:
        out += [(_chord_midi(pcs, dur) if pcs else np.zeros(int(dur * SR))), g]
    sig = np.concatenate(out); sig = sig / max(1e-9, np.max(np.abs(sig))) * 0.9
    _save(path, sig)
def write_wav_freqs(path, events, gap=0.06):
    "events = list of (list-of-frequencies, dur); plays them as chords/notes by exact frequency."
    g = np.zeros(int(gap * SR)); out = []
    for freqs, dur in events:
        s = sum(_tone_f(fr, dur) for fr in freqs); s = s / max(1e-9, np.max(np.abs(s)))
        out += [s, g]
    sig = np.concatenate(out); sig = sig / max(1e-9, np.max(np.abs(sig))) * 0.9
    _save(path, sig)
def _save(path, sig):
    with wave.open(path, 'w') as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(SR)
        w.writeframes((sig * 32767).astype('<i2').tobytes())
    print("wrote", path)

# ---------------- 12-EDO examples (MIDI + WAV) ----------------
PC = {
  "diatonic_scale":   [(p, 0.5) for p in asc(diatonic)],
  "pentatonic_scale": [(p, 0.55) for p in asc(pentatonic)],
  "even_vs_cluster":  [(p, 0.42) for p in asc(diatonic)] + [([], 0.3)]
                      + [(p, 0.42) for p in asc(cluster7)],
  "circle_of_fifths": [(p, 0.42) for p in fifths_walk()],
}
for name, ev in PC.items():
    ev_m = [(p, b) for p, b in ev if p]          # MIDI: drop the rest marker
    write_midi(name + ".mid", ev_m)
    write_wav_pc(name + ".wav", [(p if p else [], b * 0.55) for p, b in ev])

# ---------------- tuning examples (microtonal, WAV only, exact ratios) ----------------
F0 = 261.626  # middle C
def reduce_oct(f, lo=F0, hi=2*F0):
    while f >= hi: f /= 2.0
    while f < lo:  f *= 2.0
    return f
# Pythagorean comma: 12 pure fifths vs 7 octaves, then the two notes side by side (the ~23.46-cent beat)
p12 = reduce_oct(F0 * (3/2)**12)       # note reached by twelve 3:2 fifths, octave-reduced
oct7 = F0                              # seven octaves reduces back to F0
PYTH = [([F0], 0.9), ([oct7*(3/2)**1/1], 0.0)]  # placeholder; rebuilt below
PYTH = [([F0], 0.8), ([F0*2], 0.8), ([F0], 0.4),
        ([p12], 0.9), ([oct7], 0.9), ([p12, oct7], 2.4)]   # the comma: sharp note vs the octave's C, beating
write_wav_freqs("pythagorean_comma.wav", PYTH)
# Syntonic comma: pure major third 5/4 vs four fifths 81/64, side by side (the ~21.5-cent 81/80 beat)
third_just = F0 * (5/4)
third_pyth = F0 * (3/2)**4 / 4         # (81/64)
SYNT = [([F0], 0.7), ([third_just], 0.9), ([third_pyth], 0.9),
        ([third_just, third_pyth], 2.2)]
write_wav_freqs("syntonic_comma.wav", SYNT)
print("done: 4 scale + 2 tuning sonifications")
