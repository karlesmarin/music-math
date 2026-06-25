#!/usr/bin/env python3
# make_audio_phase.py - sonification companion for the phase-taxonomy note (Note #2).
# Author: Carles Marin (with Claude, Anthropic, as AI assistant).
#
# Emits, for each example, a MIDI file (primary: editable, structural) and a WAV render
# (convenience: plays without a synth, self-contained additive sine synthesis).
# The three examples let a listener HEAR the note's claims about the FOURIER PHASE:
#   z_pair          - the all-interval tetrachords 4-Z15 {0,1,4,6} and 4-Z29 {0,1,3,7}:
#                     SAME interval vector / SAME |A^|^2, yet NOT T/I-related. The phase-blind
#                     floor: interval content alone cannot tell them apart.
#   inversion_4z15  - 4-Z15 then its inversion I_0: they share 2 common tones (the held axis pair).
#   inversion_4z29  - 4-Z29 then its inversion I_0: they share 1 common tone.
#                     Together these two sonify the ISUM (sum/index vector) distinction 2 vs 1 -
#                     the PARTIAL phase that |A^|^2 discards but A^^2 retains.
# Run:  python make_audio_phase.py    (writes .mid + .wav into this directory)

import struct, wave
import numpy as np

SR = 44100

# ---------------- data (from the note, all machine-verified) ----------------
Z15 = [0, 1, 4, 6]                                # 4-Z15
Z29 = [0, 1, 3, 7]                                # 4-Z29 (homometric partner of Z15)
def T(k, S): return sorted({(x + k) % 12 for x in S})
def Inv(k, S): return sorted({(k - x) % 12 for x in S})   # I_k(x) = k - x
I0_Z15 = Inv(0, Z15)                              # {0,6,8,11}; |Z15 cap I0 Z15| = 2  ({0,6})
I0_Z29 = Inv(0, Z29)                              # {0,5,9,11}; |Z29 cap I0 Z29| = 1  ({0})

def midis(pcs, base=60): return [base + (p % 12) for p in pcs]    # pc -> MIDI, octave from C4

# ---------------- MIDI writer (pure Python, no deps) ----------------
def _vlq(n):
    out = [n & 0x7f]; n >>= 7
    while n: out.append((n & 0x7f) | 0x80); n >>= 7
    return bytes(reversed(out))

def write_midi(path, events, tpq=480, bpm=92, vel=80, gap_beats=0.15):
    "events = [(pcs, beats), ...]; one format-0 track of block chords."
    tr = bytearray()
    tr += _vlq(0) + bytes([0xFF, 0x51, 0x03]) + int(60_000_000 / bpm).to_bytes(3, 'big')  # tempo
    tr += _vlq(0) + bytes([0xC0, 0])                                                       # program: piano
    pending = 0
    for pcs, beats in events:
        ns = midis(pcs)
        for i, nt in enumerate(ns):
            tr += _vlq(pending if i == 0 else 0) + bytes([0x90, nt, vel]); pending = 0
        dur = int(beats * tpq)
        for i, nt in enumerate(ns):
            tr += _vlq(dur if i == 0 else 0) + bytes([0x80, nt, 0])
        pending = int(gap_beats * tpq)
    tr += _vlq(0) + bytes([0xFF, 0x2F, 0x00])                                              # end of track
    hdr = b'MThd' + struct.pack('>IHHH', 6, 0, 1, tpq)
    with open(path, 'wb') as f: f.write(hdr + b'MTrk' + struct.pack('>I', len(tr)) + bytes(tr))
    print("wrote", path)

# ---------------- WAV render (convenience) ----------------
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

# ---------------- the three examples (beats) ----------------
EX = {
  "z_pair":         [(Z15, 3.0), (Z29, 3.0)],            # 4-Z15 then 4-Z29: same |A^|^2, different set
  "inversion_4z15": [(Z15, 3.0), (I0_Z15, 3.0)],         # 4-Z15 vs I_0: 2 common tones
  "inversion_4z29": [(Z29, 3.0), (I0_Z29, 3.0)],         # 4-Z29 vs I_0: 1 common tone
}
for name, ev in EX.items():
    write_midi(name + ".mid", ev)                          # primary
    write_wav(name + ".wav", [(p, b * 0.5) for p, b in ev])  # render (~92bpm -> beats*0.5s)
