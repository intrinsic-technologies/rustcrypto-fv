#!/usr/bin/env python3
"""Writes long_messages.txt: ChaCha20-Poly1305 results that OpenSSL computes for messages longer
than any published vector, so `ChaCha20Poly1305/Tests.lean` can check the specification against
an implementation that shares no code with it or with the crate.

Run from this directory: python3 long_messages.py > long_messages.txt. It needs Python's
`cryptography` package, whose `ChaCha20Poly1305` is OpenSSL's (the file was written with
cryptography 41.0.7 on OpenSSL 3.0.13). Each line is one case: the message length, the associated
data length, the key, the nonce, the first 32 and last 32 bytes of the ciphertext, and the tag, in
hexadecimal. The message and associated data are not stored: byte i of the message is
(167 i + 13) mod 256, and byte i of the associated data (59 i + 101) mod 256, as `Tests.lean`
rebuilds them.
"""

from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305

CASES = [  # (message length, associated data length)
    (514, 0),          # one byte past the longest published vector (513 bytes, Wycheproof)
    (4097, 13),        # 64 blocks and one byte
    (65601, 17),       # past 2^16 bytes
    (1048639, 65537),  # past 2^20 bytes, with associated data past 2^16 bytes
]


def pattern(length, step, offset):
    return bytes((step * i + offset) % 256 for i in range(length))


for index, (message_length, data_length) in enumerate(CASES):
    key = bytes((7 * i + 3 * index + 1) % 256 for i in range(32))
    nonce = bytes((11 * i + 5 * index + 2) % 256 for i in range(12))
    sealed = ChaCha20Poly1305(key).encrypt(
        nonce, pattern(message_length, 167, 13), pattern(data_length, 59, 101))
    ciphertext, tag = sealed[:-16], sealed[-16:]
    print(message_length, data_length, key.hex(), nonce.hex(), ciphertext[:32].hex(),
          ciphertext[-32:].hex(), tag.hex())
