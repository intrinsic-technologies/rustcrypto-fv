"""Writes gctr-wrap.txt: GCTR outputs across the 32-bit counter wrap, computed with OpenSSL's AES.

Usage: python3 generate.py > gctr-wrap.txt

SP 800-38D, §6.5, Algorithm 3 computes `Y_i = X_i ⊕ CIPH_K(CB_i)` with `CB_{i+1} = inc_32(CB_i)`
(§6.2: the low 32 bits of the block are incremented modulo 2^32, the high 96 bits are unchanged).
No published vector reaches the wrap, so these values are computed here, not published: each
`CIPH_K(CB_i)` is one AES block encryption by OpenSSL through the `cryptography` package (tested
with 46.0.5), and the counter blocks are incremented by `inc32` below, written from §6.2. Each
initial counter block has its low 32-bit word near 0xffffffff, and the 32-bit word above it is
not all ones, so a counter that carried into bit 32 or beyond would give a different keystream block.
Each line is one case: the key, the initial counter block, X and the expected Y, in hex.
"""

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes


def inc32(block):
    """SP 800-38D §6.2 inc_32: MSB_96(X) || [int(LSB_32(X)) + 1 mod 2^32]_32"""
    low = (int.from_bytes(block[12:], "big") + 1) % 2**32
    return block[:12] + low.to_bytes(4, "big")


def gctr(key, icb, x):
    encryptor = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
    y = bytearray()
    cb = icb
    for i in range(0, len(x), 16):
        keystream = encryptor.update(cb)
        y += bytes(a ^ b for a, b in zip(x[i:i + 16], keystream))
        cb = inc32(cb)
    return bytes(y)


CASES = [
    # AES-128, the wrap between blocks 1 and 2, and a partial third block
    (bytes(range(16)), bytes.fromhex("0102030405060708090a0b0cffffffff"), bytes(range(0x40, 0x68))),
    # AES-128, the wrap between blocks 2 and 3
    (bytes(range(0x10, 0x20)), bytes.fromhex("cafebabedeadbeef00000000fffffffe"),
     bytes(range(0x80, 0xb0))),
    # AES-256, the wrap between blocks 1 and 2, high bits 0xff..fe so a 64-bit carry would show
    (bytes(range(0x20, 0x40)), bytes.fromhex("fffffffffffffffffffffffeffffffff"),
     bytes(range(0xc0, 0xe0))),
]

for key, icb, x in CASES:
    print(f"key={key.hex()} icb={icb.hex()} x={x.hex()} y={gctr(key, icb, x).hex()}")
