"""Writes `K256/Tests/Generated/key-files.txt` to standard output: SEC 1 `ECPrivateKey` documents
(SEC 1 v2.0 Appendix C.4, RFC 5915 §3) built by an encoder independent of the Lean specification
and of the crate, for `SecretKey::from_sec1_der`. From this directory: `python3 key-files.py >
key-files.txt`.

Each document is written by OpenSSL's ASN.1 generator (`openssl asn1parse -genconf`), and each
public key is computed by OpenSSL through Python's `cryptography` (`derive_private_key`). The
secret scalars are fixed: the leading octets of the SHA-256 digest of each line's label. The BER
documents edit one length of an OpenSSL document into a form DER forbids (X.690 §10.1). Each line
is a label, then the document in hex. The expected results are not here: `generate-vectors`
reads this file and records what the real crate returns for each document in `vectors.txt`.
"""
import hashlib
import os
import subprocess
import tempfile

from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat


def scalar(label, octets):
    """A secret scalar of `octets` octets whose first octet is not zero."""
    digest = bytearray(hashlib.sha256(label.encode()).digest()[:octets])
    digest[0] |= 0x01
    return int.from_bytes(digest, "big")


def public_key(d, compressed):
    key = ec.derive_private_key(d, ec.SECP256K1()).public_key()
    form = PublicFormat.CompressedPoint if compressed else PublicFormat.UncompressedPoint
    return key.public_bytes(Encoding.X962, form)


def document(private_key, curve, point):
    """The DER `ECPrivateKey` OpenSSL encodes from its fields; `None` leaves a field out."""
    lines = ["asn1=SEQUENCE:key", "[key]", "version=INTEGER:1",
             "privateKey=FORMAT:HEX,OCTETSTRING:" + private_key.hex()]
    if curve is not None:
        lines.append("parameters=EXPLICIT:0,OID:" + curve)
    if point is not None:
        lines.append("publicKey=EXPLICIT:1,FORMAT:HEX,BITSTRING:" + point.hex())
    with tempfile.TemporaryDirectory() as directory:
        config = os.path.join(directory, "key.cnf")
        output = os.path.join(directory, "key.der")
        with open(config, "w") as file:
            file.write("\n".join(lines) + "\n")
        subprocess.run(["openssl", "asn1parse", "-genconf", config, "-noout", "-out", output],
                       check=True)
        with open(output, "rb") as file:
            return file.read()


rows = []
# Private keys of 24 to 31 octets, in the four shapes of the optional fields
shapes = [(None, None), ("secp256k1", False), (None, True), ("secp256k1", None)]
for octets in range(24, 32):
    curve, compressed = shapes[octets % 4]
    label = f"privateKey-{octets}-octets-" + ("curve" if curve else "no-curve") + (
        "" if compressed is None else "-compressed-key" if compressed else "-key")
    d = scalar(label, octets)
    point = None if compressed is None else public_key(d, compressed)
    rows.append((label, document(d.to_bytes(octets, "big"), curve, point)))
# 32 octets: with and without the curve and the public key
for label, curve, with_key in [("privateKey-32-octets-curve-key", "secp256k1", True),
                               ("privateKey-32-octets-no-curve-key", None, True),
                               ("privateKey-32-octets-no-curve", None, False)]:
    d = scalar(label, 32)
    rows.append((label, document(d.to_bytes(32, "big"), curve, public_key(d, False) if with_key
                                 else None)))
# Refused: 23 and 33 octets, a public key of another secret, another curve
d = scalar("privateKey-23-octets-no-curve", 23)
rows.append(("privateKey-23-octets-no-curve", document(d.to_bytes(23, "big"), None, None)))
d = scalar("privateKey-33-octets-no-curve", 32)
rows.append(("privateKey-33-octets-no-curve", document(d.to_bytes(33, "big"), None, None)))
d = scalar("privateKey-33-octets-curve-key", 32)
rows.append(("privateKey-33-octets-curve-key",
             document(d.to_bytes(33, "big"), "secp256k1", public_key(d, False))))
d = scalar("public-key-of-another-secret", 32)
rows.append(("public-key-of-another-secret",
             document(d.to_bytes(32, "big"), "secp256k1", public_key(d + 1, False))))
d = scalar("curve-prime256v1", 32)
rows.append(("curve-prime256v1", document(d.to_bytes(32, "big"), "prime256v1", None)))
# BER, not DER: the 32-octet document with the curve and the key, its outer length in the long
# form (X.690 §8.1.3.5, not the fewest octets), or indefinite (§8.1.3.6); its version's length in
# the long form
der = rows[8][1]
assert der[0] == 0x30 and der[1] < 0x80 and der[2:5] == bytes([2, 1, 1])
rows.append(("ber-long-form-length", bytes([0x30, 0x81]) + der[1:]))
rows.append(("ber-indefinite-length", bytes([0x30, 0x80]) + der[2:] + bytes(2)))
rows.append(("ber-long-form-version-length",
             bytes([0x30, der[1] + 1, 2, 0x81, 1, 1]) + der[5:]))
for label, octets in rows:
    print(label, octets.hex())
