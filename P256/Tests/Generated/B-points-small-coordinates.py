#!/usr/bin/env python3
"""Print B-points-small-coordinates.txt (run: python3 B-points-small-coordinates.py > that file).

Two P-256 points with a coordinate so small that adding p still fits in 32 bytes, so that the
range check of SEC 1 §2.3.4 (each coordinate below p) is what rejects `x + p` or `y + p`. The
curve is SP 800-186 §3.2.1.3's, y² = x³ − 3x + b mod p; this computation is independent of the
Lean specifications. Each line is `x y`, 32 bytes each, in hexadecimal:
- line 1: the least x ≥ 0 that is the x of a point, and y = (x³ − 3x + b)^((p + 1)/4) mod p;
- line 2: the least y ≥ 1 that is the y of a point, and one x of it, a root of x³ − 3x + b − y²
  found by a gcd with x^p − x and, for several roots, an equal-degree split.
"""
p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b


def rhs(x):
    return (x * x * x - 3 * x + b) % p


def sqrt(v):
    r = pow(v, (p + 1) // 4, p)
    return r if r * r % p == v else None


def trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def pmod(f, g):
    """f mod g, polynomials as coefficient lists, lowest degree first"""
    f = trim(f[:])
    while len(f) >= len(g):
        q = f[-1] * pow(g[-1], -1, p) % p
        s = len(f) - len(g)
        for i, a in enumerate(g):
            f[s + i] = (f[s + i] - q * a) % p
        trim(f)
    return f


def pmulmod(f, g, m):
    r = [0] * (len(f) + len(g))
    for i, a in enumerate(f):
        for j, c in enumerate(g):
            r[i + j] = (r[i + j] + a * c) % p
    return pmod(r, m)


def ppowmod(base, e, m):
    result = [1]
    while e:
        if e & 1:
            result = pmulmod(result, base, m)
        base = pmulmod(base, base, m)
        e >>= 1
    return result


def gcd(f, g):
    f, g = trim(f[:]), trim(g[:])
    while g:
        f, g = g, pmod(f, g)
    inverse = pow(f[-1], -1, p)
    return [a * inverse % p for a in f]


def sub(f, g):
    n = max(len(f), len(g))
    f, g = f + [0] * (n - len(f)), g + [0] * (n - len(g))
    return trim([(a - c) % p for a, c in zip(f, g)])


def cubic_root(c):
    """a root of x³ − 3x + c mod p, or None"""
    f = [c % p, p - 3, 0, 1]
    h = gcd(f, sub(ppowmod([0, 1], p, f), [0, 1]))
    a = 0
    while len(h) > 2:
        split = gcd(h, sub(ppowmod([a, 1], (p - 1) // 2, h), [1]))
        if 1 < len(split) < len(h):
            h = split
        a += 1
    return None if len(h) < 2 else (-h[0]) % p


x = 0
while sqrt(rhs(x)) is None:
    x += 1
print(f"{x:064x} {sqrt(rhs(x)):064x}")

y = 1
while (root := cubic_root(b - y * y)) is None:
    y += 1
assert rhs(root) == y * y % p
print(f"{root:064x} {y:064x}")
