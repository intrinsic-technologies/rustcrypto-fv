#!/usr/bin/env python3
"""Generator of P256/Tests/Generated/D-ecdsa-cases.txt, an independent computation of the ECDSA
values the signature tests expect where no standard prints them: DER signatures, recovery IDs and
recovered keys.

Plain Python, sharing no code with the Lean specifications: P-256 from SP 800-186 §3.2.1.3, the
group law and ECDSA signing, verification and recovery from SEC 1 v2.0 §§2.2.1, 4.1.3, 4.1.4 and
4.1.6, RFC 6979 §3.2 nonces with §3.6 additional data (HMAC-SHA-256, Python's `hmac` and
`hashlib`), and the DER encoding of `ECDSA-Sig-Value` (SEC 1 v2.0 Appendix C.5, X.690 §§8.3 and
8.9). Each line is `label hex`. Run:
`python3 P256/Tests/Generated/D-ecdsa-generator.py > P256/Tests/Generated/D-ecdsa-cases.txt`.
"""
import hashlib
import hmac

p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
n = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
a = p - 3
b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
G = (0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
     0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)


def add(P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    if P[0] == Q[0] and (P[1] + Q[1]) % p == 0:
        return None
    if P == Q:
        m = (3 * P[0] * P[0] + a) * pow(2 * P[1], -1, p) % p
    else:
        m = (Q[1] - P[1]) * pow(Q[0] - P[0], -1, p) % p
    x = (m * m - P[0] - Q[0]) % p
    return (x, (m * (P[0] - x) - P[1]) % p)


def mul(k, P):
    R = None
    while k:
        if k & 1:
            R = add(R, P)
        P = add(P, P)
        k >>= 1
    return R


def lift(x, odd):
    """The point with this x and y parity, else None"""
    if x >= p:
        return None
    rhs = (x ** 3 + a * x + b) % p
    y = pow(rhs, (p + 1) // 4, p)
    if y * y % p != rhs:
        return None
    return (x, y if y % 2 == odd else p - y)


def be(value, size=32):
    return value.to_bytes(size, 'big')


def uncompressed(P):
    return b'\x04' + be(P[0]) + be(P[1])


def der_integer(value):
    body = value.to_bytes(max(1, (value.bit_length() + 7) // 8), 'big')
    if body[0] & 0x80:
        body = b'\x00' + body
    return b'\x02' + bytes([len(body)]) + body


def der(r, s):
    body = der_integer(r) + der_integer(s)
    return b'\x30' + bytes([len(body)]) + body


def bits2int(data):
    value = int.from_bytes(data, 'big')
    excess = 8 * len(data) - 256
    return value >> excess if excess > 0 else value


def rfc6979_nonces(x, h1, extra):
    """RFC 6979 §3.2 steps b to h with the §3.6 additional data `extra`"""
    h1 = be(bits2int(h1) % n)
    V, K = b'\x01' * 32, b'\x00' * 32
    seed = be(x) + h1 + extra
    K = hmac.new(K, V + b'\x00' + seed, hashlib.sha256).digest()
    V = hmac.new(K, V, hashlib.sha256).digest()
    K = hmac.new(K, V + b'\x01' + seed, hashlib.sha256).digest()
    V = hmac.new(K, V, hashlib.sha256).digest()
    while True:
        V = hmac.new(K, V, hashlib.sha256).digest()
        k = int.from_bytes(V, 'big')
        if 1 <= k < n:
            yield k
        K = hmac.new(K, V + b'\x00', hashlib.sha256).digest()
        V = hmac.new(K, V, hashlib.sha256).digest()


def sign(x, prehash, extra=b''):
    """SEC 1 §4.1.3 with RFC 6979 nonces; (r, s, recovery ID); no low-s normalization"""
    e = bits2int(prehash) % n
    for k in rfc6979_nonces(x, prehash, extra):
        R = mul(k, G)
        r = R[0] % n
        s = pow(k, -1, n) * (e + r * x) % n
        if r and s:
            return r, s, 2 * (R[0] >= n) + R[1] % 2


def verify(Q, prehash, r, s):
    e = bits2int(prehash) % n
    w = pow(s, -1, n)
    R = add(mul(e * w % n, G), mul(r * w % n, Q))
    return R is not None and R[0] % n == r


def recover(prehash, r, s, recovery_id):
    """SEC 1 §4.1.6 for one recovery ID: x(R) = r (+ n for bit 1), y parity bit 0; else None"""
    R = lift(r + n * (recovery_id >> 1), recovery_id & 1)
    if R is None:
        return None
    e = bits2int(prehash) % n
    inverse = pow(r, -1, n)
    return add(mul((-e * inverse) % n, G), mul(s * inverse % n, R))


def line(label, data):
    print(label, data.hex())


x = 0xc9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721
Q = mul(x, G)
messages = {m: hashlib.sha256(m.encode()).digest() for m in ('sample', 'test')}

for message, prehash in messages.items():
    r, s, recovery_id = sign(x, prehash)
    assert verify(Q, prehash, r, s)
    line(f'rfc6979-{message}-der', der(r, s))
    line(f'rfc6979-{message}-id', bytes([recovery_id]))
    for other in range(4):
        key = recover(prehash, r, s, other)
        line(f'rfc6979-{message}-recover-id{other}', uncompressed(key) if key else b'')

sample = messages['sample']

t = next(t for t in range(1, 1000) if lift(t + n, 0))
assert t + n < p
for recovery_id in (2, 3):
    key = recover(sample, t, 7, recovery_id)
    line(f'recover-small-r-id{recovery_id}-signature', be(t) + be(7))
    line(f'recover-small-r-id{recovery_id}-key', uncompressed(key))
    assert verify(key, sample, t, 7)
wrap = next(u for u in range(1, 1000) if lift(u, 0))
r_wrap = 2 ** 256 - n + wrap
assert r_wrap < n
line('recover-wrapping-r-signature', be(r_wrap) + be(7))
line('recover-wrapping-r-id0-key', uncompressed(recover(sample, r_wrap, 7, 0)))
line('recover-r-p-minus-n-signature', be(p - n) + be(7))

# u1 G + u2 R is the identity: R = kG, r = x(R), s = e / k, so r^-1 (s R - e G) = O; SEC 1 §4.1.6
# then has no key for the recovery ID naming R (step 1.6.1 gives O, not a public key)
k = 7
R = mul(k, G)
assert R[0] < n
e = bits2int(sample) % n
s_identity = e * pow(k, -1, n) % n
identity_id = R[1] % 2
assert recover(sample, R[0], s_identity, identity_id) is None
line('recover-identity-signature', be(R[0]) + be(s_identity))
line('recover-identity-id', bytes([identity_id]))
for other in range(4):
    key = recover(sample, R[0], s_identity, other)
    line(f'recover-identity-id{other}-key', uncompressed(key) if key else b'')
