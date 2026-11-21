# Standards

Shared Lean definitions of published standards, organized by publisher and subject. Import
`Standards` for everything or a subject module such as `Standards.SECG.ECC`. The tables list only
the formalized parts of each document.

## NIST

| Directory | Formalized coverage | Original document |
| --- | --- | --- |
| [NIST/AES](NIST/AES/) | GF(2⁸) arithmetic, SBOX and INVSBOX from their defining formulas, the round transformations and their inverses, KEYEXPANSION, and CIPHER for AES-128, AES-192, and AES-256 | [FIPS 197-upd1](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf), §§3.3–3.5, 4.2–4.4, 5–5.2, and 5.3.1–5.3.4 (Table 3 and Eq. (5.1) in §5; not INVCIPHER of §5.3 or §5.3.5, EQINVCIPHER) |
| [NIST/EllipticCurves](NIST/EllipticCurves/) | P-256 domain parameters; prime-field arithmetic and inverses; square roots modulo a prime `p ≡ 3 mod 4` | [SP 800-186](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf), §§3.1.2 and 3.2.1.3 and Appendices E.3 and E.4 |
| [NIST/GCM](NIST/GCM/) | GHASH and GCM's authenticated encryption and decryption functions for any block cipher with 128-bit blocks: the bit-string operations of §6.1 (`0^s`, ⊕, LSB, MSB, the right shift, and the integer-to-string and string-to-integer functions), the incrementing function inc_s, the block product of Algorithm 1 with R, GHASH of Algorithm 2 on a sequence of 128-bit blocks (the empty sequence included), GCTR, the pre-counter block J_0, the tag, and GCM-AE and GCM-AD. GCM-AE and GCM-AD take any supported lengths (including the largest that §5.2.1.1 allows) and any tag length up to 128 bits; of these tag lengths, the document allows only the seven of §5.2.1.2. Byte strings are read as bit strings as in FIPS 197-upd1 §3.3, which SP 800-38D does not state. GMAC is not formalized | [SP 800-38D](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf), §§5.2, 6.1–6.5 and 7 |
| [NIST/SHA1](NIST/SHA1/) | SHA-1 of bit strings; the padding, parsing, `Ch`, `Maj` and the digest type are shared with NIST/SHA2 | [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf), §§3.2, 4.1.1, 4.2.1, 5.1.1, 5.2.1, 5.3.1 and 6.1 |
| [NIST/SHA2](NIST/SHA2/) | SHA-224, SHA-256, SHA-384, and SHA-512 of bit strings, and SHA-256 of octet strings | [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf), §§3–6.5 |
| [NIST/SHA2](NIST/SHA2/Truncated.lean) | SHA-512/224 and SHA-512/256 of bit strings | [FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf), §§5.3.6.1–5.3.6.2, 6.6, and 6.7 |
| [NIST/SHA3](NIST/SHA3/) | KECCAK-p and KECCAK-f for every state width, the sponge construction, pad10*1, KECCAK[c], SHA3-224, SHA3-256, SHA3-384, and SHA3-512 of bit strings; conversions between byte strings and bit strings | [FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf), §§2.3, 3–5, 6.1, and Appendix B.1 |

## SECG

| Directory | Formalized coverage | Original document |
| --- | --- | --- |
| [SECG/ECC](SECG/ECC/) | Curve arithmetic over prime fields, including negation; integer and point encodings; public-key validation, key derivation, raw ECDH, and ECDSA. Callers supply the domain parameters, the hash, and square roots | [SEC 1 v2.0](https://www.secg.org/sec1-v2.pdf), §§2, 3.2–3.3.1, 4.1–4.1.4, and Appendix C.4 |
| [SECG/DomainParameters](SECG/DomainParameters/) | The secp256k1 domain parameters | [SEC 2 v2.0](https://www.secg.org/sec2-v2.pdf), §2.4.1 |

## RFC

| Directory | Formalized coverage | Original document |
| --- | --- | --- |
| [RFC/HMAC](RFC/HMAC/) | HMAC parameterized by its hash and block size | [RFC 2104](https://www.rfc-editor.org/rfc/rfc2104.html), §2 |
| [RFC/DeterministicSigning](RFC/DeterministicSigning/) | Integer conversions, the HMAC state transitions that generate the nonce, and the signing retries and results, parameterized by the hash, the order, and a signing callback; the §3.6 variant that appends additional data `k'` to the HMAC input, in step d and also in step f, a reading of §3.6 that the definition's documentation labels as an interpretation | [RFC 6979](https://www.rfc-editor.org/rfc/rfc6979.html), §§2.3, 3.2 and 3.6 |
| [RFC/BaseEncodings](RFC/BaseEncodings/) | Base 16 (upper- and lowercase) encoding, padded and unpadded; decoding that rejects bad characters and padding, with zero pad bits required and optionally case-insensitive | [RFC 4648](https://www.rfc-editor.org/rfc/rfc4648.html), §§3, 8, and 10 |
| [RFC/MD5](RFC/MD5/) | The MD5 message digest of bit strings, its padding, buffer, and block processing | [RFC 1321](https://www.rfc-editor.org/rfc/rfc1321.html), §§2–3.5 |
| [RFC/HKDF](RFC/HKDF/) | HKDF-Extract and HKDF-Expand parameterized by the hash function, including the `255 * HashLen` limit; the instance at SHA-256 | [RFC 5869](https://www.rfc-editor.org/rfc/rfc5869.html), §§2.2–2.3 |
| [RFC/ChaCha20Poly1305](RFC/ChaCha20Poly1305/) | Poly1305: `le_bytes_to_num`, `num_to_16_le_bytes`, the clamping of `r`, and `poly1305_mac` of a message of any length, the empty message included, under a 32-byte one-time key, following the pseudocode with verified [Erratum 5689](https://www.rfc-editor.org/errata/eid5689). ChaCha20: the quarter round on four words and on the state, the state setup, `inner_block`, `chacha20_block` with its serialization, and `chacha20_encrypt` of a plaintext of any length from any 32-bit initial counter, with the counter sum taken modulo 2^32, following the pseudocode with verified [Erratum 5989](https://www.rfc-editor.org/errata/eid5989) (concatenation) and [Erratum 7880](https://www.rfc-editor.org/errata/eid7880) (the slice of the last block). The Poly1305 key generation `poly1305_key_gen`. AEAD_CHACHA20_POLY1305: `pad16`, `num_to_8_le_bytes`, the Poly1305 input, `chacha20_aead_encrypt` with a 96-bit nonce, and decryption, which compares the tag. Not in the RFC: the state setup, block function and encryption also take any four words 12–15, and a block counter of any number of 32-bit words that wraps at its width, so that the original ChaCha layout of a 64-bit nonce and a 64-bit block count (§2.3) is an instance of the same block function. The AEAD is also tested against [Project Wycheproof](https://github.com/C2SP/wycheproof/tree/e0df04e0c033f2d25c5051dd06230336c7822358)'s `chacha20_poly1305_test.json`, whose vectors include empty and 16-byte-multiple AADs and ciphertexts | [RFC 8439](https://www.rfc-editor.org/rfc/rfc8439.html), §§2.1–2.6 and 2.8, with the examples of §§2.1–2.6.2 and 2.8.2 and Appendices A.1–A.5 |
