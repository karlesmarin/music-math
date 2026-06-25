# Exact verification: in Z_24, the coset H_k saturates |a_k| = gcd(24,k).
# Author: Carles Marin (with Claude, Anthropic, as AI assistant).
# Confirms the microtonal Appendix-A table of spectral_note: each saturating coset H_k = (N/gcd)*Z_N
# realises |a_k| = gcd(24,k) exactly, and identifies the off-12-grid mode (H_8, odd quarter tones).
N = 24
z = CyclotomicField(N).gen()   # exact primitive 24th root of unity
def ahat(A, k):
    return sum(z**((k*j) % N) for j in A)
def H(k):
    g = gcd(N, k); step = N // g
    return sorted({(step*j) % N for j in range(N)})
ok = True
for k in [3,4,6,8,12]:
    Hk = H(k); g = gcd(N,k)
    val = ahat(Hk, k)
    mag2 = QQbar(val).abs()**2
    odd = [q for q in Hk if q % 2 == 1]
    print("k=%2d gcd=%2d |H_k|=%2d |a_k|^2=%s saturated=%s off12grid=%s odd=%s"
          % (k, g, len(Hk), mag2, mag2==g*g, 'YES' if odd else 'no', odd))
    ok = ok and (mag2 == g*g) and (len(Hk)==g)
print("ALL SATURATED + CARD=gcd:", ok)
