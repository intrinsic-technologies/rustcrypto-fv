"""Writes `K256/Tests/Generated/low-s-bound.txt` to standard output: four ECDSA signatures on
secp256k1 whose `s` is BIP 62's low-`s` bound or one more, built and checked independently of the
Lean specification and of the crate, for `Verifier::verify`. From this directory:
`python3 low-s-bound.py > low-s-bound.txt`.

A signature with a chosen `s` is built by choosing the key: for a fixed nonce `k` (the SHA-256
digest of the line's label, reduced mod `n`), `r = x(k · G) mod n` with `k · G` computed by
OpenSSL through Python's `cryptography` (`derive_private_key`), and the secret
`d = r⁻¹ (s · k − e) mod n` for the SHA-256 digest `e` of the message, so that `(r, s)` is a SEC 1
signature under `d · G` (SEC 1 v2.0 §4.1.4: `e s⁻¹ · G + r s⁻¹ · d · G = k · G`). The pair is
`s = 0x7FFF…20A0`, BIP 62's largest low `s` ("Low S values in signatures": "between 0x1 and
0x7FFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF 5D576E73 57A4501D DFE92F46 681B20A0 (inclusive)"), and
`s = 0x7FFF…20A1`, one more; each also appears in the form `n − s` under the same key, an
equivalent signature (SEC 1 §4.1.3), which swaps the two values of `s`.

Each line is a label, the public key's 65-byte uncompressed SEC 1 encoding (OpenSSL's), the
message, the signature `r ‖ s`, OpenSSL's SEC 1 verdict (`valid` or `invalid`), and the status
`verify` must give: 0 if OpenSSL finds the signature valid and `s` is at most BIP 62's bound, 1
otherwise. The crate's own verdicts are not here.
"""
import hashlib

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import encode_dss_signature
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat

# The order of secp256k1's generator, SEC 2 v2.0 §2.4.1
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
# BIP 62, "Low S values in signatures": the largest `s` a low-`s` signature may have
BIP62_LARGEST_S = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0

MESSAGE = b"k256 low-s bound"
E = int.from_bytes(hashlib.sha256(MESSAGE).digest(), "big")


def signed(label, s):
    """The public key under which `(r, s)` signs `MESSAGE`, and `r`, for the label's nonce."""
    k = int.from_bytes(hashlib.sha256(label.encode()).digest(), "big") % N
    r = ec.derive_private_key(k, ec.SECP256K1()).public_key().public_numbers().x % N
    d = pow(r, -1, N) * (s * k - E) % N
    assert 0 < r and 0 < d
    return ec.derive_private_key(d, ec.SECP256K1()).public_key(), r


def line(label, key, r, s):
    try:
        key.verify(encode_dss_signature(r, s), MESSAGE, ec.ECDSA(hashes.SHA256()))
        valid = True
    except InvalidSignature:
        valid = False
    status = 0 if valid and s <= BIP62_LARGEST_S else 1
    point = key.public_bytes(Encoding.X962, PublicFormat.UncompressedPoint)
    signature = r.to_bytes(32, "big") + s.to_bytes(32, "big")
    print(label, point.hex(), MESSAGE.hex(), signature.hex(), "valid" if valid else "invalid",
          status)


at_bound, r = signed("s-is-the-bound", BIP62_LARGEST_S)
line("s-is-the-bound", at_bound, r, BIP62_LARGEST_S)
line("s-is-the-bound-negated", at_bound, r, N - BIP62_LARGEST_S)
above_bound, r = signed("s-is-the-bound-plus-1", BIP62_LARGEST_S + 1)
line("s-is-the-bound-plus-1", above_bound, r, BIP62_LARGEST_S + 1)
line("s-is-the-bound-plus-1-negated", above_bound, r, N - BIP62_LARGEST_S - 1)
