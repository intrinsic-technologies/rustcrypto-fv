/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import X86.UserProcess.CodeImage

namespace Sha1.Spec.Program.Extracted

/-- The link-time address of the symbol `sha1_compress` -/
def sha1CompressAddress : BitVec 64 := 0x100000

/-- An estimated stack budget for the symbol `sha1_compress`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha1CompressStackBytes : Option Nat := some 336

/-- The link-time address of the symbol `sha1_digest` -/
def sha1DigestAddress : BitVec 64 := 0x100010

/-- An estimated stack budget for the symbol `sha1_digest`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha1DigestStackBytes : Option Nat := some 656

/-- The link-time address of the symbol `sha1_finalize_fixed_reset` -/
def sha1FinalizeFixedResetAddress : BitVec 64 := 0x1002c0

/-- An estimated stack budget for the symbol `sha1_finalize_fixed_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha1FinalizeFixedResetStackBytes : Option Nat := some 608

/-- The link-time address of the symbol `sha1_finalize_into_reset` -/
def sha1FinalizeIntoResetAddress : BitVec 64 := 0x100970

/-- An estimated stack budget for the symbol `sha1_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha1FinalizeIntoResetStackBytes : Option Nat := some 608

/-- The link-time address of the symbol `sha1_finalize_reset` -/
def sha1FinalizeResetAddress : BitVec 64 := 0x101010

/-- An estimated stack budget for the symbol `sha1_finalize_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha1FinalizeResetStackBytes : Option Nat := some 704

/-- The link-time address of the symbol `sha1_reset` -/
def sha1ResetAddress : BitVec 64 := 0x101710

/-- An estimated stack budget for the symbol `sha1_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha1ResetStackBytes : Option Nat := some 704

/-- The link-time address of the symbol `sha1_update_finalize` -/
def sha1UpdateFinalizeAddress : BitVec 64 := 0x101c30

/-- An estimated stack budget for the symbol `sha1_update_finalize`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha1UpdateFinalizeStackBytes : Option Nat := some 704

/-- The link-time address of the symbol `sha1_update_reset` -/
def sha1UpdateResetAddress : BitVec 64 := 0x101fd0

/-- An estimated stack budget for the symbol `sha1_update_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha1UpdateResetStackBytes : Option Nat := some 704

end Sha1.Spec.Program.Extracted
