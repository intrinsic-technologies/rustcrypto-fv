#!/usr/bin/env python3
"""Writes md5_long.txt: finalizations of an `Md5Core` whose block count is 2^23 or more, so the
message is at least 2^32 bits long. Run from this directory:
python3 generate_long.py > md5_long.txt

Each line is a core state in its 24-byte serialized form (the MD buffer A, B, C, D, then the block
count, each low-order byte first), a tail length n, and the MD5 digest of the message whose first
64 * count bytes leave that buffer, followed by the first n bytes of the pattern i % 251.

* "hashlib" lines need no MD5 code here. X is a run of zero bytes, a whole number k of blocks,
  and P its RFC 1321 padding, one block. Python's hashlib gives the digest of X as the buffer after
  X || P, k + 1 blocks, and the digest of X || P || tail as the expected value. k + 1 is 2^23
  (a bit length of exactly 2^32) or 2^23 + 1.
* "rfc" lines take block counts no hashed message reaches, up to 2^64 - 1. Their digest is the
  RFC 1321 padding and block loop below, written from the RFC and not from the Lean definitions, and
  checked here against every "hashlib" line and against hashlib on 0 to 200 byte messages.
"""

import hashlib
import math
import struct

PATTERN = bytes(i % 251 for i in range(200))
TAILS = (0, 1, 5, 55, 56, 63)

T = [int(abs(math.sin(i + 1)) * 2**32) & 0xFFFFFFFF for i in range(64)]
S = [7, 12, 17, 22] * 4 + [5, 9, 14, 20] * 4 + [4, 11, 16, 23] * 4 + [6, 10, 15, 21] * 4
INITIAL = (0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476)


def rotl(x, s):
    return ((x << s) | (x >> (32 - s))) & 0xFFFFFFFF


def process_block(buffer, block):
    """RFC 1321, section 3.4, on one 64-byte block"""
    X = struct.unpack("<16I", block)
    a, b, c, d = buffer
    for i in range(64):
        if i < 16:
            f, k = (b & c) | (~b & d), i
        elif i < 32:
            f, k = (b & d) | (c & ~d), (1 + 5 * i) % 16
        elif i < 48:
            f, k = b ^ c ^ d, (5 + 3 * i) % 16
        else:
            f, k = c ^ (b | (~d & 0xFFFFFFFF)), (7 * i) % 16
        f &= 0xFFFFFFFF
        a, b, c, d = d, (b + rotl((a + f + X[k] + T[i]) & 0xFFFFFFFF, S[i])) & 0xFFFFFFFF, b, c
    return tuple((x + y) & 0xFFFFFFFF for x, y in zip(buffer, (a, b, c, d)))


def padding(byte_length):
    """RFC 1321, sections 3.1 and 3.2, for a message of byte_length bytes"""
    zeros = (55 - byte_length) % 64
    return b"\x80" + bytes(zeros) + struct.pack("<Q", (8 * byte_length) % 2**64)


def finalize(buffer, count, tail):
    """The digest from `buffer` after `count` blocks, then `tail`, padded"""
    data = tail + padding(64 * count + len(tail))
    for i in range(0, len(data), 64):
        buffer = process_block(buffer, data[i : i + 64])
    return struct.pack("<4I", *buffer)


def core(buffer_bytes, count):
    return buffer_bytes + struct.pack("<Q", count % 2**64)


for n in range(201):
    assert finalize(INITIAL, 0, PATTERN[:n]) == hashlib.md5(PATTERN[:n]).digest()

print("# serialized core, tail length n, digest; from generate_long.py")
CHUNK = bytes(2**20)
for blocks in (2**23 - 1, 2**23):
    prefix = hashlib.md5()
    for _ in range(64 * blocks // len(CHUNK)):
        prefix.update(CHUNK)
    prefix.update(bytes(64 * blocks % len(CHUNK)))
    buffer_bytes = prefix.digest()
    prefix.update(padding(64 * blocks))
    for n in TAILS:
        extended = prefix.copy()
        extended.update(PATTERN[:n])
        expected = extended.digest()
        buffer = struct.unpack("<4I", buffer_bytes)
        assert finalize(buffer, blocks + 1, PATTERN[:n]) == expected
        print("hashlib", core(buffer_bytes, blocks + 1).hex(), n, expected.hex())

RFC_COUNTS = (2**32 - 1, 2**32, 2**32 + 1, 2**57 - 1, 2**58 - 1, 2**58 + 1,
              0x0123456789ABCDEF, 2**63, 2**64 - 1)
for index, count in enumerate(RFC_COUNTS):
    buffer_bytes = hashlib.md5(PATTERN[:index]).digest()
    buffer = struct.unpack("<4I", buffer_bytes)
    for n in TAILS:
        print("rfc", core(buffer_bytes, count).hex(), n, finalize(buffer, count, PATTERN[:n]).hex())
