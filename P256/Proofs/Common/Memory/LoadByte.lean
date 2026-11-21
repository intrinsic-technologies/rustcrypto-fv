import X86Proofs.Program.Execution

set_option autoImplicit false

namespace P256.Proofs.Common.Memory

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memLoad8_of_byte {memory : Ram} {address : BitVec 64} {byte : UInt8}
    (h : memory[address]? = some byte) : memLoad memory address 8 = byte.toBitVec := by
  simp [memLoad, List.range_succ, memByte, PhysicalMemory.read, h]

end P256.Proofs.Common.Memory
