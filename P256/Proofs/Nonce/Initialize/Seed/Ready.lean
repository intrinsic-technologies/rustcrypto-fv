import P256.Proofs.Nonce.Initialize.Seed.SerializeCall.Result

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure UpdateReady [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) (value : Nat) : Prop where
  stage : Stage initial s boundary
  rip : s.RIP = 0x107c15
  order : s.regValue .r15 = orderAddress
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  destination : s.regValue .rdi = stackPtr s + 8
  descriptors : s.regValue .rsi = stackPtr s + 104
  count : s.regValue .rdx = 3
  secretPointer : memLoad s.external (stackPtr s + 104) 64 = initial.regValue .rsi
  secretLength : memLoad s.external (stackPtr s + 112) 64 = 32
  reducedPointer : memLoad s.external (stackPtr s + 120) 64 = stackPtr s + 200
  reducedLength : memLoad s.external (stackPtr s + 128) 64 = 32
  entropyLength : memLoad s.external (stackPtr s + 144) 64 = 0
  octets : (MemoryRegion.mk (stackPtr s + 200).toNat 32).HasBytes s.external
    (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n value)
  drbg : DrbgAt s (stackPtr s + 8) ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩

  outputPointer : s.regValue .r14 = initial.regValue .rdi

end P256.Proofs.Nonce.Initialize.Seed
