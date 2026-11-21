import P256.Proofs.Verifying.Core.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open Prelude X86 X86.Machine X86Proofs
open SecretKeyFromBytes.Scalar

theorem operand_write_reg_external (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

theorem operand_write_mem_external (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

theorem nat256_word_copy {s t : RamState} {source destination : BitVec 64} {value : Nat}
    (input : Nat256At s source value) (readable : MemReadable t destination 32)
    (words : ∀ k < 4, memLoad t.external (destination+BitVec.ofNat 64 (8*k)) 64 =
      memLoad s.external (source+BitVec.ofNat 64 (8*k)) 64) :
    Nat256At t destination value := by
  apply nat256At_of_memLoad_limbs input.1 readable.mem
  intro k hk
  exact (words k hk).trans (input.memLoad_limb k hk)

end P256.Proofs.Verifying.Core.Scalars
