/- Generated using lean-x86's extraction utility; do not modify this file directly. -/

import X86.UserProcess.CodeImage

namespace Sha2.Spec.Program.Extracted

/-- The link-time address of the symbol `sha224_digest` -/
def sha224DigestAddress : BitVec 64 := 0x100000

/-- An estimated stack budget for the symbol `sha224_digest`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha224DigestStackBytes : Option Nat := some 784

/-- The link-time address of the symbol `sha224_digest_slices` -/
def sha224DigestSlicesAddress : BitVec 64 := 0x1002b0

/-- An estimated stack budget for the symbol `sha224_digest_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha224DigestSlicesStackBytes : Option Nat := some 816

/-- The link-time address of the symbol `sha224_finalize_into_reset` -/
def sha224FinalizeIntoResetAddress : BitVec 64 := 0x100650

/-- An estimated stack budget for the symbol `sha224_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha224FinalizeIntoResetStackBytes : Option Nat := some 832

/-- The link-time address of the symbol `sha224_reset` -/
def sha224ResetAddress : BitVec 64 := 0x100d30

/-- An estimated stack budget for the symbol `sha224_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha224ResetStackBytes : Option Nat := some 720

/-- The link-time address of the symbol `sha224_trait_finalize_fixed_reset` -/
def sha224TraitFinalizeFixedResetAddress : BitVec 64 := 0x100d30

/-- An estimated stack budget for the symbol `sha224_trait_finalize_fixed_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha224TraitFinalizeFixedResetStackBytes : Option Nat := some 720

/-- The link-time address of the symbol `sha224_trait_finalize_into_reset` -/
def sha224TraitFinalizeIntoResetAddress : BitVec 64 := 0x1014d0

/-- An estimated stack budget for the symbol `sha224_trait_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha224TraitFinalizeIntoResetStackBytes : Option Nat := some 832

/-- The link-time address of the symbol `sha256_digest` -/
def sha256DigestAddress : BitVec 64 := 0x101bf0

/-- An estimated stack budget for the symbol `sha256_digest`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha256DigestStackBytes : Option Nat := some 784

/-- The link-time address of the symbol `sha256_digest_slices` -/
def sha256DigestSlicesAddress : BitVec 64 := 0x101eb0

/-- An estimated stack budget for the symbol `sha256_digest_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha256DigestSlicesStackBytes : Option Nat := some 816

/-- The link-time address of the symbol `sha256_finalize_into_reset` -/
def sha256FinalizeIntoResetAddress : BitVec 64 := 0x102260

/-- An estimated stack budget for the symbol `sha256_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha256FinalizeIntoResetStackBytes : Option Nat := some 832

/-- The link-time address of the symbol `sha256_reset` -/
def sha256ResetAddress : BitVec 64 := 0x102960

/-- An estimated stack budget for the symbol `sha256_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha256ResetStackBytes : Option Nat := some 720

/-- The link-time address of the symbol `sha256_trait_finalize_fixed_reset` -/
def sha256TraitFinalizeFixedResetAddress : BitVec 64 := 0x102960

/-- An estimated stack budget for the symbol `sha256_trait_finalize_fixed_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha256TraitFinalizeFixedResetStackBytes : Option Nat := some 720

/-- The link-time address of the symbol `sha256_trait_finalize_into_reset` -/
def sha256TraitFinalizeIntoResetAddress : BitVec 64 := 0x103120

/-- An estimated stack budget for the symbol `sha256_trait_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha256TraitFinalizeIntoResetStackBytes : Option Nat := some 832

/-- The link-time address of the symbol `sha2_compress256` -/
def sha2Compress256Address : BitVec 64 := 0x103860

/-- An estimated stack budget for the symbol `sha2_compress256`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha2Compress256StackBytes : Option Nat := some 464

/-- The link-time address of the symbol `sha2_compress512` -/
def sha2Compress512Address : BitVec 64 := 0x103870

/-- An estimated stack budget for the symbol `sha2_compress512`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha2Compress512StackBytes : Option Nat := some 544

/-- The link-time address of the symbol `sha384_digest` -/
def sha384DigestAddress : BitVec 64 := 0x103880

/-- An estimated stack budget for the symbol `sha384_digest`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha384DigestStackBytes : Option Nat := some 1152

/-- The link-time address of the symbol `sha384_digest_slices` -/
def sha384DigestSlicesAddress : BitVec 64 := 0x103b80

/-- An estimated stack budget for the symbol `sha384_digest_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha384DigestSlicesStackBytes : Option Nat := some 1184

/-- The link-time address of the symbol `sha384_finalize_into_reset` -/
def sha384FinalizeIntoResetAddress : BitVec 64 := 0x103f70

/-- An estimated stack budget for the symbol `sha384_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha384FinalizeIntoResetStackBytes : Option Nat := some 1184

/-- The link-time address of the symbol `sha384_reset` -/
def sha384ResetAddress : BitVec 64 := 0x1046f0

/-- An estimated stack budget for the symbol `sha384_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha384ResetStackBytes : Option Nat := some 976

/-- The link-time address of the symbol `sha384_trait_finalize_fixed_reset` -/
def sha384TraitFinalizeFixedResetAddress : BitVec 64 := 0x1046f0

/-- An estimated stack budget for the symbol `sha384_trait_finalize_fixed_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha384TraitFinalizeFixedResetStackBytes : Option Nat := some 976

/-- The link-time address of the symbol `sha384_trait_finalize_into_reset` -/
def sha384TraitFinalizeIntoResetAddress : BitVec 64 := 0x104fc0

/-- An estimated stack budget for the symbol `sha384_trait_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha384TraitFinalizeIntoResetStackBytes : Option Nat := some 1200

/-- The link-time address of the symbol `sha512_digest` -/
def sha512DigestAddress : BitVec 64 := 0x109490

/-- An estimated stack budget for the symbol `sha512_digest`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512DigestStackBytes : Option Nat := some 1152

/-- The link-time address of the symbol `sha512_digest_slices` -/
def sha512DigestSlicesAddress : BitVec 64 := 0x1097b0

/-- An estimated stack budget for the symbol `sha512_digest_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512DigestSlicesStackBytes : Option Nat := some 1184

/-- The link-time address of the symbol `sha512_finalize_into_reset` -/
def sha512FinalizeIntoResetAddress : BitVec 64 := 0x109bc0

/-- An estimated stack budget for the symbol `sha512_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512FinalizeIntoResetStackBytes : Option Nat := some 1184

/-- The link-time address of the symbol `sha512_reset` -/
def sha512ResetAddress : BitVec 64 := 0x10a380

/-- An estimated stack budget for the symbol `sha512_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512ResetStackBytes : Option Nat := some 976

/-- The link-time address of the symbol `sha512_trait_finalize_fixed_reset` -/
def sha512TraitFinalizeFixedResetAddress : BitVec 64 := 0x10a380

/-- An estimated stack budget for the symbol `sha512_trait_finalize_fixed_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512TraitFinalizeFixedResetStackBytes : Option Nat := some 976

/-- The link-time address of the symbol `sha512_trait_finalize_into_reset` -/
def sha512TraitFinalizeIntoResetAddress : BitVec 64 := 0x10ac90

/-- An estimated stack budget for the symbol `sha512_trait_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512TraitFinalizeIntoResetStackBytes : Option Nat := some 1200

/-- The link-time address of the symbol `sha512_224_digest` -/
def sha512_224DigestAddress : BitVec 64 := 0x1057d0

/-- An estimated stack budget for the symbol `sha512_224_digest`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_224DigestStackBytes : Option Nat := some 1152

/-- The link-time address of the symbol `sha512_224_digest_slices` -/
def sha512_224DigestSlicesAddress : BitVec 64 := 0x105ab0

/-- An estimated stack budget for the symbol `sha512_224_digest_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_224DigestSlicesStackBytes : Option Nat := some 1184

/-- The link-time address of the symbol `sha512_224_finalize_into_reset` -/
def sha512_224FinalizeIntoResetAddress : BitVec 64 := 0x105e80

/-- An estimated stack budget for the symbol `sha512_224_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_224FinalizeIntoResetStackBytes : Option Nat := some 1184

/-- The link-time address of the symbol `sha512_224_reset` -/
def sha512_224ResetAddress : BitVec 64 := 0x1065c0

/-- An estimated stack budget for the symbol `sha512_224_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_224ResetStackBytes : Option Nat := some 976

/-- The link-time address of the symbol `sha512_224_trait_finalize_fixed_reset` -/
def sha512_224TraitFinalizeFixedResetAddress : BitVec 64 := 0x1065c0

/-- An estimated stack budget for the symbol `sha512_224_trait_finalize_fixed_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_224TraitFinalizeFixedResetStackBytes : Option Nat := some 976

/-- The link-time address of the symbol `sha512_224_trait_finalize_into_reset` -/
def sha512_224TraitFinalizeIntoResetAddress : BitVec 64 := 0x106e60

/-- An estimated stack budget for the symbol `sha512_224_trait_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_224TraitFinalizeIntoResetStackBytes : Option Nat := some 1200

/-- The link-time address of the symbol `sha512_256_digest` -/
def sha512_256DigestAddress : BitVec 64 := 0x107630

/-- An estimated stack budget for the symbol `sha512_256_digest`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_256DigestStackBytes : Option Nat := some 1152

/-- The link-time address of the symbol `sha512_256_digest_slices` -/
def sha512_256DigestSlicesAddress : BitVec 64 := 0x107910

/-- An estimated stack budget for the symbol `sha512_256_digest_slices`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_256DigestSlicesStackBytes : Option Nat := some 1184

/-- The link-time address of the symbol `sha512_256_finalize_into_reset` -/
def sha512_256FinalizeIntoResetAddress : BitVec 64 := 0x107ce0

/-- An estimated stack budget for the symbol `sha512_256_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_256FinalizeIntoResetStackBytes : Option Nat := some 1184

/-- The link-time address of the symbol `sha512_256_reset` -/
def sha512_256ResetAddress : BitVec 64 := 0x108420

/-- An estimated stack budget for the symbol `sha512_256_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_256ResetStackBytes : Option Nat := some 976

/-- The link-time address of the symbol `sha512_256_trait_finalize_fixed_reset` -/
def sha512_256TraitFinalizeFixedResetAddress : BitVec 64 := 0x108420

/-- An estimated stack budget for the symbol `sha512_256_trait_finalize_fixed_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_256TraitFinalizeFixedResetStackBytes : Option Nat := some 976

/-- The link-time address of the symbol `sha512_256_trait_finalize_into_reset` -/
def sha512_256TraitFinalizeIntoResetAddress : BitVec 64 := 0x108cc0

/-- An estimated stack budget for the symbol `sha512_256_trait_finalize_into_reset`: the bytes below its entry RSP that it and its callees use. A proof must check it. -/
def sha512_256TraitFinalizeIntoResetStackBytes : Option Nat := some 1200

end Sha2.Spec.Program.Extracted
