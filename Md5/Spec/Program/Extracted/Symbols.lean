/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import X86.UserProcess.CodeImage

namespace Md5.Spec.Program.Extracted

/-- The link-time address of the symbol `md5_compress` -/
def md5CompressAddress : BitVec 64 := 0x100000

/-- An estimated stack budget for the symbol `md5_compress`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5CompressStackBytes : Option Nat := some 312

/-- The link-time address of the symbol `md5_digest` -/
def md5DigestAddress : BitVec 64 := 0x100010

/-- An estimated stack budget for the symbol `md5_digest`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5DigestStackBytes : Option Nat := some 616

/-- The link-time address of the symbol `md5_digest_slices` -/
def md5DigestSlicesAddress : BitVec 64 := 0x100290

/-- An estimated stack budget for the symbol `md5_digest_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5DigestSlicesStackBytes : Option Nat := some 664

/-- The link-time address of the symbol `md5_digest_slices_reset` -/
def md5DigestSlicesResetAddress : BitVec 64 := 0x100600

/-- An estimated stack budget for the symbol `md5_digest_slices_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5DigestSlicesResetStackBytes : Option Nat := some 696

/-- The link-time address of the symbol `md5_finalize_fixed_reset_slices` -/
def md5FinalizeFixedResetSlicesAddress : BitVec 64 := 0x100600

/-- An estimated stack budget for the symbol `md5_finalize_fixed_reset_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5FinalizeFixedResetSlicesStackBytes : Option Nat := some 696

/-- The link-time address of the symbol `md5_finalize_into_reset_slices` -/
def md5FinalizeIntoResetSlicesAddress : BitVec 64 := 0x100cb0

/-- An estimated stack budget for the symbol `md5_finalize_into_reset_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5FinalizeIntoResetSlicesStackBytes : Option Nat := some 680

/-- The link-time address of the symbol `md5_fixed_finalize_into_reset_slices` -/
def md5FixedFinalizeIntoResetSlicesAddress : BitVec 64 := 0x100cb0

/-- An estimated stack budget for the symbol `md5_fixed_finalize_into_reset_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5FixedFinalizeIntoResetSlicesStackBytes : Option Nat := some 680

/-- The link-time address of the symbol `md5_reset_slices` -/
def md5ResetSlicesAddress : BitVec 64 := 0x101340

/-- An estimated stack budget for the symbol `md5_reset_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5ResetSlicesStackBytes : Option Nat := some 680

/-- The link-time address of the symbol `md5_update_finalize_into` -/
def md5UpdateFinalizeIntoAddress : BitVec 64 := 0x101840

/-- An estimated stack budget for the symbol `md5_update_finalize_into`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5UpdateFinalizeIntoStackBytes : Option Nat := some 648

/-- The link-time address of the symbol `md5_update_reset_slices` -/
def md5UpdateResetSlicesAddress : BitVec 64 := 0x101340

/-- An estimated stack budget for the symbol `md5_update_reset_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def md5UpdateResetSlicesStackBytes : Option Nat := some 680

end Md5.Spec.Program.Extracted
