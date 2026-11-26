"""Independent middle-range bound. Only the slab parameters are read."""

from bisect import bisect_left
from functools import lru_cache
from itertools import accumulate, product
import json
from math import comb, factorial, isqrt, prod
from pathlib import Path
import sys

from flint import arb, ctx


ctx.prec = 256
CUT = 100000
prime = bytearray([1]) * (CUT + 1)
prime[:2] = bytes(2)
for p in range(2, isqrt(CUT) + 1):
    if prime[p]:
        prime[p*p::p] = bytes((CUT - p*p) // p + 1)
primes = [p for p in range(3, CUT + 1) if prime[p]]


@lru_cache(maxsize=None)
def prime_range(u, v):
    """Upper S=sum 1/(p-1), lower V, upper J=sum 1/(p(p-1))."""
    small = primes[bisect_left(primes, u):bisect_left(primes, v)]
    S = sum((arb(1) / (p - 1) for p in small), arb(0))
    V = prod((1 - arb(1) / (p - 1) for p in small), start=arb(1))
    J = sum((arb(1) / (p * (p - 1)) for p in small), arb(0))
    u = max(u, CUT + 1)
    if v > u:
        a, b = arb(u).log(), arb(v).log()
        upper = (2 / (arb(v).sqrt() * b) if v <= 10**12
                 else arb("0.000006836") / b)
        extra = arb(1) / (u - 1)
        tail = (b / a).log() + upper + arb("0.000002964") / a + extra
        S += tail
        J += extra
        V *= (-tail - arb(1) / (u - 2)).exp()
    return S, V, J


def pi_upper(x):
    if x <= CUT:
        return arb(bisect_left(primes, x + 1) + int(x >= 2))
    t = arb(x)
    return t / (t.log() - 2) + t.sqrt() * t.log() / (8 * arb.pi())


def slab(r):
    lo, hi = int(r["x_lo"]), int(r["x_hi"])
    z, y, a = int(r["z"]), int(r["y"]), r["a"]
    if not (lo < hi and primes[a-1] < z < y and min(y**5, z*y**4) >= hi):
        raise ValueError("weight or slab range")
    L = arb(lo).log()
    root = arb(lo).sqrt()
    # GRH: JS 5.1, Schoenfeld, and omega(N) <= log(N)/log(2).
    rho = (arb("0.16") + 1 / (16 * arb.pi())) * L**2 / root + L**2 / (lo * arb(2).log())
    errfactor = {}
    support = {}
    for side, parity, multiplier in (("low", 1, 1), ("up", 0, y)):
        caps, ends = r[side + "_caps"], r[side + "_ends"]
        if (not caps or len(ends) != len(caps)+1 or ends[0] != z or ends[-1] != primes[a-1]+1
                or any(c < 0 or c % 2 != parity for c in caps)
                or sorted(caps) != caps or any(b >= t for t, b in zip(ends, ends[1:]))):
            raise ValueError("cap structure")
        level = multiplier * prod(primes[:a])
        e = arb(0)
        sizes = []
        for j, cap in enumerate(caps):
            level *= ends[j] ** (cap - (caps[j-1] if j else 0))
            S, V, _ = prime_range(ends[j+1], z)
            e += S**(cap+1) / (factorial(cap+1) * V)
            sizes.append(int(pi_upper(ends[j]-1).upper().ceil().unique_fmpz()))
        if level**2 > lo:
            raise ValueError("modulus exceeds GRH range")
        support[side] = 2**a * sum(
            prod(comb(n, k) for n, k in zip(sizes, counts))
            for counts in product(*(range(min(n, cap)+1) for n, cap in zip(sizes, caps)))
            if all(k <= cap for k, cap in zip(accumulate(counts), caps))
        )
        errfactor[side] = e
    S, _, J = prime_range(z, y)
    bracket = 1 - errfactor["low"] - (1 + errfactor["up"]) * S / 2
    if not bracket > 0:
        raise ValueError("nonpositive bracket")
    _, density, _ = prime_range(3, z)
    count = pi_upper(y)
    # Expand each upper sieve directly with X=|A|/(q-1); r(qd) is then its only remainder.
    err = rho * (support["low"] + count * support["up"] / 2)
    if y**4 <= lo:
        ratio = L/(L-2) + L**2/(8*arb.pi()*root)
        err += (ratio * J + count * rho) / 2
    else:
        err += arb(hi).log() * J / 2
    return density * bracket - err


def check(path):
    if not arb(CUT).li() < arb(CUT) / (arb(CUT).log() - 2):
        raise ValueError("base point of the logarithmic integral bound")
    rows = json.loads(path.read_text(encoding="utf-8"))
    end = 4 * 10**18
    if len(rows) != 58:
        raise ValueError("slab count")
    minima = []
    for r in rows:
        if int(r["x_lo"]) != end:
            raise ValueError("slab gap")
        margin = slab(r)
        if not margin > 0:
            raise ValueError(f"nonpositive lower bound at {end}: {margin}")
        minima.append(int((margin * 10**9).lower().floor().unique_fmpz()))
        end = int(r["x_hi"])
    if end != 10**500:
        raise ValueError("wrong final endpoint")
    print(f"58 slabs passed; uniform lower bound {min(minima)}/10^9")


if __name__ == "__main__":
    check(Path(sys.argv[1]))
