#!/usr/bin/env python3
# make_audio.py - sonification companion for "Diabolus in Machina" (Note #3 / the spectral essay).
# Author: Carles Marin (with Claude, Anthropic, as AI assistant).
#
# Each example is the audible form of one protagonist / theorem of the essay. Emits a MIDI file
# (editable, structural) and a self-contained additive-sine WAV (plays without a synth):
#   diabolus            - the tritone alone, then the C/F# bitonal (Petrushka) chord (the leitmotif).
#   augmented_cycle     - Liszt: the four augmented triads that exhaust the 12 notes (the a_3=sqrt5 axis).
#   tonnetz_hexatonic   - Wagner: a P-L walk on the Tonnetz (the hexatonic cycle; walking the graph).
#   petrushka_octatonic - Stravinsky: the octatonic scale, then the 6-30 / Petrushka chord.
#   axis_bartok         - Bartok: the diminished-seventh axis {0,3,6,9} and its two tritone pillars.
#   modes_messiaen      - Messiaen: the whole-tone then the octatonic mode (the symmetric scales).
#   tritone_symmetry    - 6-30 and its T6 transpose: the same six pitch classes (the fixed point, heard).
# Run:  python make_audio.py    (writes .mid + .wav into this directory)

import struct, wave
import numpy as np

SR = 44100

# ---------------- pitch-class helpers ----------------
def T(k, S): return sorted({(x + k) % 12 for x in S})
def midis(pcs, base=60): return [base + (p % 12) for p in pcs]

Cmaj, Fsmaj = [0, 4, 7], [6, 10, 1]
petrushka = sorted(set(Cmaj) | set(Fsmaj))          # {0,1,4,6,7,10} = 6-30B
A630 = [0, 1, 3, 6, 7, 9]                            # 6-30 = (013679)
octatonic = [0, 1, 3, 4, 6, 7, 9, 10]
wholetone = [0, 2, 4, 6, 8, 10]
dim7 = [0, 3, 6, 9]
aug_triads = [[0, 4, 8], [1, 5, 9], [2, 6, 10], [3, 7, 11]]

# neo-Riemannian transforms on (root, is_major): triad set = major {r,r+4,r+7} / minor {r,r+3,r+7}
def triad(root, maj): return sorted({(root) % 12, (root + (4 if maj else 3)) % 12, (root + 7) % 12})
def P(s): r, m = s; return (r, not m)
def L(s):
    r, m = s
    return ((r + 4) % 12, False) if m else ((r - 4) % 12, True)
# hexatonic cycle from C major by alternating P, L  (Cmaj Cmin Abmaj Abmin Emaj Emin -> Cmaj)
def hexatonic():
    s = (0, True); seq = [s]
    for i in range(6):
        s = P(s) if i % 2 == 0 else L(s); seq.append(s)
    return [triad(r, m) for (r, m) in seq]

def melody(pcs, oct_top=True):
    "ascending scale as single notes; optionally add the top octave"
    seq = [[p] for p in pcs]
    if oct_top: seq.append([pcs[0]])
    return seq

# ---------------- MIDI writer (pure Python) ----------------
def _vlq(n):
    out = [n & 0x7f]; n >>= 7
    while n: out.append((n & 0x7f) | 0x80); n >>= 7
    return bytes(reversed(out))

def write_midi(path, events, tpq=480, bpm=92, vel=80, gap_beats=0.15):
    tr = bytearray()
    tr += _vlq(0) + bytes([0xFF, 0x51, 0x03]) + int(60_000_000 / bpm).to_bytes(3, 'big')
    tr += _vlq(0) + bytes([0xC0, 0])
    pending = 0
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
def _freq(m): return 440.0 * 2.0 ** ((m - 69) / 12.0)
def _tone(m, dur):
    n = int(dur * SR); t = np.arange(n) / SR; f = _freq(m)
    y = np.sin(2*np.pi*f*t) + 0.5*np.sin(2*np.pi*2*f*t) + 0.25*np.sin(2*np.pi*3*f*t)
    a = max(1, int(0.012 * SR)); env = np.ones(n)
    env[:a] = np.linspace(0, 1, a); env[-a:] = np.linspace(1, 0, a)
    return y * env
def _chord(pcs, dur):
    s = sum(_tone(m, dur) for m in midis(pcs)); return s / max(1e-9, np.max(np.abs(s)))
def write_wav(path, events, gap=0.10):
    g = np.zeros(int(gap * SR)); out = []
    for pcs, dur in events: out += [_chord(pcs, dur), g]
    sig = np.concatenate(out); sig = sig / max(1e-9, np.max(np.abs(sig))) * 0.9
    with wave.open(path, 'w') as w:
        w.setnchannels(1); w.setsampwidth(2); w.setframerate(SR)
        w.writeframes((sig * 32767).astype('<i2').tobytes())
    print("wrote", path)

# ---------------- the examples ----------------
EX = {
  "diabolus":            [([0], 1.2), ([6], 1.2), ([0, 6], 2.0), (petrushka, 3.0)],
  "augmented_cycle":     [(t, 1.4) for t in aug_triads] + [(aug_triads[0], 1.4)],
  "tonnetz_hexatonic":   [(t, 1.6) for t in hexatonic()],
  "petrushka_octatonic": [(p, 0.5) for p in melody(octatonic)] + [(petrushka, 3.0)],
  "axis_bartok":         [(dim7, 2.5), ([0, 6], 1.5), ([3, 9], 1.5), (dim7, 2.5)],
  "modes_messiaen":      [(p, 0.45) for p in melody(wholetone)] + [(p, 0.4) for p in melody(octatonic)],
  "tritone_symmetry":    [(A630, 3.0), (T(6, A630), 3.0)],
}
for name, ev in EX.items():
    write_midi(name + ".mid", ev)
    write_wav(name + ".wav", [(p, b * 0.5) for p, b in ev])
print("done:", len(EX), "examples")
