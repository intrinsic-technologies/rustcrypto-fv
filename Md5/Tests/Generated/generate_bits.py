#!/usr/bin/env python3
"""Writes md5_bits.txt: the MD5 digest of the first n bits of the pattern byte i = i mod 251,
taken high-order bit first (RFC 1321, section 2), for n from 0 to 1040, so every bit length mod 8
and every padding case near one and two blocks, including n = 447 and 959, where the padding is a
single 1 bit and no 0 bits. hashlib takes only whole bytes, so the digests come from the RFC 1321
code below, written from the RFC's text (sections 3.1 to 3.5), which this script first checks
against hashlib on every whole-byte length it writes. Run from this directory:
python3 generate_bits.py > md5_bits.txt"""

import hashlib
import math

PATTERN = bytes(i % 251 for i in range(200))

# Section 3.4: T[i] is the integer part of 4294967296 * abs(sin(i)), i in radians.
T = [int(4294967296 * abs(math.sin(i))) & 0xFFFFFFFF for i in range(1, 65)]
# Section 3.4: the shift amounts of each round, in the order the operations print them.
S = [[7, 12, 17, 22], [5, 9, 14, 20], [4, 11, 16, 23], [6, 10, 15, 21]]


def rotl(x, s):
    return ((x << s) | (x >> (32 - s))) & 0xFFFFFFFF


def word_index(i):
    """The message word of operation i, 0 to 63, in the RFC's [abcd k s i] lists."""
    r, j = divmod(i, 16)
    return [j, (1 + 5 * j) % 16, (5 + 3 * j) % 16, (7 * j) % 16][r]


def auxiliary(r, x, y, z):
    if r == 0:
        return (x & y) | (~x & z & 0xFFFFFFFF)
    if r == 1:
        return (x & z) | (y & ~z & 0xFFFFFFFF)
    if r == 2:
        return x ^ y ^ z
    return y ^ (x | (~z & 0xFFFFFFFF))


def md5_bits(bits):
    """MD5 of a list of bits (sections 3.1 to 3.5)."""
    b = len(bits)
    padded = bits + [1]  # Section 3.1: one 1 bit, then 0 bits to 448 mod 512.
    while len(padded) % 512 != 448:
        padded.append(0)
    length = b % 2**64  # Section 3.2: low-order word first, each word low-order byte first.
    for byte in length.to_bytes(8, "little"):
        padded += [(byte >> (7 - k)) & 1 for k in range(8)]
    data = bytes(
        sum(padded[8 * i + k] << (7 - k) for k in range(8)) for i in range(len(padded) // 8)
    )
    a0, b0, c0, d0 = 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476  # Section 3.3.
    for start in range(0, len(data), 64):
        X = [int.from_bytes(data[start + 4 * j : start + 4 * j + 4], "little") for j in range(16)]
        a, b_, c, d = a0, b0, c0, d0
        for i in range(64):
            r = i // 16
            f = auxiliary(r, b_, c, d)
            new = (b_ + rotl((a + f + X[word_index(i)] + T[i]) & 0xFFFFFFFF, S[r][i % 4]))
            a, b_, c, d = d, new & 0xFFFFFFFF, b_, c
        a0, b0 = (a0 + a) & 0xFFFFFFFF, (b0 + b_) & 0xFFFFFFFF
        c0, d0 = (c0 + c) & 0xFFFFFFFF, (d0 + d) & 0xFFFFFFFF
    return b"".join(w.to_bytes(4, "little") for w in (a0, b0, c0, d0)).hex()  # Section 3.5.


def pattern_bits(n):
    return [(PATTERN[i // 8] >> (7 - i % 8)) & 1 for i in range(n)]


for n in range(0, 1041, 8):
    assert md5_bits(pattern_bits(n)) == hashlib.md5(PATTERN[: n // 8]).hexdigest(), n

print("# n, then the MD5 of the first n bits of bytes(i % 251 for i in range(200)), high-order")
print("# bit first, by the RFC 1321 code of generate_bits.py, checked against hashlib on whole bytes")
for n in range(1041):
    print(n, md5_bits(pattern_bits(n)))
