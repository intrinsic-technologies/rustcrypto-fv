import Standards.RFC.BaseEncodings

/-!
# `base16ct` results in terms of RFC 4648

What `base16ct` 1.0.0 returns, in terms of RFC 4648 as `Standards.RFC.BaseEncodings` defines it: its
two encoders and three decoders, its `Error` type, and how its functions classify a rejected input.
Base 16 has no pad characters (RFC 4648, §8), so `.unpadded` and `.padded` give the same results;
this file uses `.unpadded` throughout.

RFC 4648 only says that a decoder rejects data; it does not name errors. The split between
`Error::InvalidLength` and `Error::InvalidEncoding`, and which check comes first, is the crate's
own, read from `decode_inner` in `base16ct-1.0.0/src/lib.rs`. The alphabets of the three
decoders are read from `decode_nibble` in `lower.rs`, `upper.rs` and `mixed.rs`; `Tests.lean`
checks each decoder against RFC 4648 Table 5 on all 65,536 two-character inputs.

Source: https://www.rfc-editor.org/rfc/rfc4648
-/

namespace Base16ct.Spec.Base16

open Standards.RFC.BaseEncodings

/-- The errors of `base16ct::Error` (`base16ct-1.0.0/src/error.rs`), in declaration order -/
inductive Error where
  /-- `Error::InvalidEncoding`: a character outside the decoder's alphabet -/
  | invalidEncoding
  /--
  `Error::InvalidLength`: an odd number of characters, or an output buffer shorter than the
  result. The crate documents this variant as "Insufficient output buffer length." but also
  returns it for odd input lengths; RFC 4648 rejects those inputs either way.
  -/
  | invalidLength
  deriving DecidableEq, Repr

/--
Encoder of `base16ct::lower`: RFC 4648 §8 encoding over Table 5 with `a`–`f` for `A`–`F`
(`Alphabet.base16Lower`), two characters per octet, high 4 bits first
-/
def lowerEncoder (input : ByteArray) : ByteArray :=
  encode .base16Lower .unpadded input

/--
Encoder of `base16ct::upper`: RFC 4648 §8 encoding over Table 5, `0`–`9`, `A`–`F`, two
characters per octet, high 4 bits first
-/
def upperEncoder (input : ByteArray) : ByteArray :=
  encode .base16Upper .unpadded input

/--
Decoder of `base16ct::lower`: RFC 4648 §8 decoding over the lowercase alphabet `0`–`9`,
`a`–`f`, so `A`–`F` are outside the alphabet and rejected (§3.3)
-/
def lowerDecoder (encoded : ByteArray) : Option ByteArray :=
  decode .base16Lower .unpadded encoded

/--
Decoder of `base16ct::upper`: RFC 4648 §8 decoding over Table 5, `0`–`9`, `A`–`F`, so `a`–`f`
are outside the alphabet and rejected (§3.3)
-/
def upperDecoder (encoded : ByteArray) : Option ByteArray :=
  decode .base16Upper .unpadded encoded

/--
Decoder of `base16ct::mixed`: `decodeIgnoringCase` over Table 5, which accepts `0`–`9` and
`A`–`F` in either case, mixed within one input. This is the departure from RFC 4648 §3.3 that
`decodeIgnoringCase` documents. RFC 4648 §8 calls Base16 "the standard case-insensitive hex
encoding", and the crate's `mixed` module provides it ("Function for decoding mixed Base16
(hex)", `base16ct-1.0.0/src/lib.rs`).
-/
def mixedDecoder (encoded : ByteArray) : Option ByteArray :=
  decodeIgnoringCase .base16Upper .unpadded encoded

/--
Number of octets that `encodedLength` base 16 characters decode to, or `none` for an odd count,
which no base 16 encoding has (RFC 4648, §8: "The encoding process represents 8-bit groups
(octets) of input bits as output strings of 2 encoded characters."). `base16ct::decoded_len`
returns `Error::InvalidLength` for `none`.
-/
def decodedLength (encodedLength : Nat) : Option Nat :=
  if encodedLength % 2 = 0 then some (encodedLength / 2) else none

/--
Result of decoding `encoded` with `decoder` into an output buffer of `outputCapacity` bytes, as
`decode_inner` does for `base16ct::{lower, upper, mixed}::decode`: the decoded octets, which fill
the start of the buffer, or the error. Lengths are checked before characters:

1. an odd number of characters gives `invalidLength` (`decoded_len`)
2. a buffer shorter than half the characters gives `invalidLength` (`get_mut`)
3. otherwise a character `decoder` rejects gives `invalidEncoding`

For a well-formed alphabet, an even-length input that `decoder` rejects has a character outside
the alphabet, so step 3 is the RFC's §3.3 rejection.
-/
def decodeInto (decoder : ByteArray → Option ByteArray) (encoded : ByteArray)
    (outputCapacity : Nat) : Except Error ByteArray :=
  match decodedLength encoded.size with
  | none => .error .invalidLength
  | some length =>
    if outputCapacity < length then .error .invalidLength
    else
      match decoder encoded with
      | some output => .ok output
      | none => .error .invalidEncoding

end Base16ct.Spec.Base16
