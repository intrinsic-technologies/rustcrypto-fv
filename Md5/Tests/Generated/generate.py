#!/usr/bin/env python3
"""Writes md5_lengths.txt: the MD5 digest, by Python's hashlib, of the first n bytes of the
pattern byte i = i mod 251, for n from 0 to 200. Run from this directory:
python3 generate.py > md5_lengths.txt"""

import hashlib

PATTERN = bytes(i % 251 for i in range(200))

print("# n, then hashlib.md5 of bytes(i % 251 for i in range(n)), from generate.py")
for n in range(201):
    print(n, hashlib.md5(PATTERN[:n]).hexdigest())
