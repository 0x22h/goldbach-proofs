"""Direct majorants for both Rosser boundary sums under K <= 81/80."""

from fractions import Fraction
from math import isqrt, prod

from flint import arb, ctx


H = 100  # bins per unit of log D / log z
S = 10   # both functions equal 1/s^3 above S
P = 10**12  # integer units per unit of function value
END = H * S


def ceil_ratio(n, d):
    return -(-n // d)


def step(other, odd):
    # suffix[j] / (P*H) = integral from j/H to infinity.
    suffix = [0] * (END + 1)
    suffix[END] = P * H // (2 * S**2)
    for j in reversed(range(END)):
        suffix[j] = suffix[j + 1] + other[j]
    result = [0] * END
    for i in range(H if odd else 2 * H, END):
        if odd and i < 3 * H:
            bound = ceil_ratio(
                (3 * 81 * 80 * H - 6400 * i) * P
                + 3 * 81 * H * other[2 * H] + 81**2 * suffix[2 * H],
                6400 * i,
            )
        else:
            j = i - H
            bound = ceil_ratio(i * other[j] + 81 * suffix[j], 80 * i)
        result[i] = max(P // S**3, bound)
    return result


def majorants():
    if P % S**3 or (P * H) % (2 * S**2):
        raise ValueError("the tail boundary and its integral must be exact integers")
    odd = even = [0] * END
    for iteration in range(1, 1001):
        new_odd, new_even = step(even, True), step(odd, False)
        if (new_odd, new_even) == (odd, even):
            break
        odd, even = new_odd, new_even
    else:
        raise ValueError("no discrete supersolution found")
    # Check the witness independently using the rational formulas in referee.md.
    K = Fraction(81, 80)
    ratio = Fraction(S, S - 1)
    if (K - 1) * ratio**3 + K * ratio**2 / 2 > 1:
        raise ValueError("unbounded tail fails")
    for own, other, start in ((odd, even, H), (even, odd, 2 * H)):
        integral = [Fraction(0)] * (END + 1)
        integral[END] = Fraction(1, 2 * S**2)
        for j in reversed(range(END)):
            integral[j] = integral[j + 1] + Fraction(other[j], H * P)
        for i in range(start, END):
            s, value = Fraction(i, H), Fraction(own[i], P)
            next_value = Fraction(own[i + 1], P) if i + 1 < END else Fraction(1, S**3)
            if value < next_value:
                raise ValueError(f"monotonicity at {s}")
            if i >= END - H and value > Fraction(H, i + 1)**3:
                raise ValueError(f"tail transition at {s}")
            if start == H and s < 3:
                rhs = 3 * K / s - 1 + 3 * K / s * (
                    (K - 1) * Fraction(other[2 * H], P) + K * integral[2 * H] / 3
                )
            else:
                rhs = (K - 1) * Fraction(other[i - H], P) + K / s * integral[i - H]
            if rhs > value:
                raise ValueError(f"recursion at {s}")
    print(f"exact supersolution on {2 * END - 3 * H} bins; {iteration} iterations")
    return odd, even


def presieve():
    """Verify every closed prime interval up to B and bound the remainder via S3 D."""
    B = 10**7
    primality = bytearray([1]) * (B+1)
    primality[:2] = bytes(2)
    for p in range(2, isqrt(B)+1):
        if primality[p]:
            primality[p*p::p] = bytes((B-p*p)//p+1)
    excluded = [p for p in range(3, 83, 2) if primality[p]] + [103, 107, 191, 223]
    Q = prod(excluded)
    removed = set(excluded)
    zero = arb(0)
    ending = worst = zero
    previous = None
    for p in range(3, B+1, 2):
        if not primality[p] or p in removed:
            continue
        t = arb(p).log().log()
        residual = (ending + previous - t).upper() if previous is not None else zero
        ending = (max(zero, residual) + (1 + arb(1)/(p-2)).log()).upper()
        worst = max(worst, ending)
        previous = t
    # S3 D: for this even B, each of delta_B and delta'_B is below this common bound.
    upper_tail = 2/(arb(B).sqrt()*arb(B).log()) + arb("0.000009800")/arb(10**12).log() + arb(2)/(B-1)
    limit = (arb(81)/80).log()
    if not worst + upper_tail < limit:
        raise ValueError("all-interval presieve fails")
    print(f"closed-prime intervals: log excess including analytic tail <= {(worst + upper_tail).upper()}")
    # A lower bound for V(z) log(z), uniformly for z > 10^12.
    u = 100001
    prefix = prod((1-arb(1)/(p-1) for p in range(3,u,2) if primality[p]), start=arb(1))
    loss = arb("0.000009800")/arb(u).log() + arb(1)/(u-1) + arb(1)/(u-2)
    if not prefix*arb(u).log()*(-loss).exp() > arb("0.7"):
        raise ValueError("density lower bound")
    return Q


def at(table, arg, lower):
    if not arg >= lower:
        raise ValueError("argument below domain")
    if arg >= S:
        return 1 / arg**3
    index = int((arg * H).lower().floor().unique_fmpz())
    return arb(table[index]) / P


def check():
    ctx.prec = 192
    odd, even = majorants()
    Q = presieve()
    L = arb(10).log() * 500
    X = 10**500
    alpha = arb(64)/625
    for m in (22, 24):
        beta = arb(m-1)/(4*m)
        z0 = (L/m).exp()
        s = m*(arb(1)/2-alpha)
        if not (alpha*L - 4*L.log() > arb(Q).log() and alpha*L > 4 and z0 > 10**12
                and s > 2 and s-m*beta > 1 and 5*beta > 1 and L > 2*m):
            raise ValueError("uniform tail hypotheses")
        half_sum = arb(0)
        count = 2000
        width = (beta-arb(1)/m)/count
        for j in range(count):
            a = arb(1)/m + j*width
            b = arb(1)/m + (j+1)*width
            reciprocal_sum = z0/(z0-1) * ((b/a).log() + arb("0.000009800")/(a*L))
            half_sum += (1 + at(odd, s-m*b, 1)) * reciprocal_sum/2
        bracket = 1 - at(even, s, 2) - half_sum
        if not bracket > 0:
            raise ValueError("nonpositive bracket")
        coeff = arb("0.16") + 1/(16*arb.pi()) + 1/(arb(X).sqrt()*arb(2).log())
        # Units M*N/log(N)^2. Use H=sqrt(N)/log(N)^4; no squarefree-density saving.
        mod_error = 3*coeff/(2*m*L)
        squares = L**2/(2*m*(z0-1))
        net = arb("0.7")*bracket - mod_error - squares
        if not net > 0:
            raise ValueError("nonpositive tail")
        print(f"M={m}: bracket {bracket}, net {net} (units M*N/log(N)^2)")


if __name__ == "__main__":
    check()
