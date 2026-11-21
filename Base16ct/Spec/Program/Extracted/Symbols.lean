/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import X86.UserProcess.CodeImage

namespace Base16ct.Spec.Program.Extracted

/-- The link-time address of the symbol `base16ct_decoded_len` -/
def decoded_lenAddress : BitVec 64 := 0x100000

/-- An estimated stack budget for the symbol `base16ct_decoded_len`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def decoded_lenStackBytes : Option Nat := some 128

/-- The link-time address of the symbol `base16ct_encoded_len` -/
def encoded_lenAddress : BitVec 64 := 0x100020

/-- An estimated stack budget for the symbol `base16ct_encoded_len`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def encoded_lenStackBytes : Option Nat := some 128

/-- The link-time address of the symbol `base16ct_lower_decode` -/
def lower_decodeAddress : BitVec 64 := 0x100030

/-- An estimated stack budget for the symbol `base16ct_lower_decode`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def lower_decodeStackBytes : Option Nat := some 144

/-- The link-time address of the symbol `base16ct_lower_encode` -/
def lower_encodeAddress : BitVec 64 := 0x100140

/-- An estimated stack budget for the symbol `base16ct_lower_encode`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def lower_encodeStackBytes : Option Nat := some 160

/-- The link-time address of the symbol `base16ct_lower_encode_str` -/
def lower_encode_strAddress : BitVec 64 := 0x100180

/-- An estimated stack budget for the symbol `base16ct_lower_encode_str`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def lower_encode_strStackBytes : Option Nat := some 160

/-- The link-time address of the symbol `base16ct_mixed_decode` -/
def mixed_decodeAddress : BitVec 64 := 0x1001c0

/-- An estimated stack budget for the symbol `base16ct_mixed_decode`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def mixed_decodeStackBytes : Option Nat := some 152

/-- The link-time address of the symbol `base16ct_upper_decode` -/
def upper_decodeAddress : BitVec 64 := 0x100310

/-- An estimated stack budget for the symbol `base16ct_upper_decode`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def upper_decodeStackBytes : Option Nat := some 144

/-- The link-time address of the symbol `base16ct_upper_encode` -/
def upper_encodeAddress : BitVec 64 := 0x100420

/-- An estimated stack budget for the symbol `base16ct_upper_encode`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def upper_encodeStackBytes : Option Nat := some 160

/-- The link-time address of the symbol `base16ct_upper_encode_str` -/
def upper_encode_strAddress : BitVec 64 := 0x100460

/-- An estimated stack budget for the symbol `base16ct_upper_encode_str`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def upper_encode_strStackBytes : Option Nat := some 160

end Base16ct.Spec.Program.Extracted
