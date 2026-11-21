import P256.Proofs.SHA256.State
import P256.Proofs.SHA256.Compression.Frame

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def blockComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7,
    .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
    .rip, .flags, .mem (stackPtr s) 192, .mem (stackPtr s + 208) 80]

structure BlockPre (s : RamState) (hash : Array UInt32) (block : ByteArray) : Prop where
  stack : FramePre 0x1159e0 10114 288 s
  registers : RegistersAt s hash
  inputReadable : MemReadable s (s.regValue .rsi) 64
  inputBytes : (registerRegion s .rsi 64).HasBytes s.external block
  inputSeparate : RangeApart (s.regValue .rsi) 64 (stackPtr s) 288
  frameAvoids : ∀ i < 288, ¬ InProgram (stackPtr s + BitVec.ofNat 64 i)

structure BlockResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt32) (block : ByteArray) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  rip : t.RIP = 0x118162
  rsp : stackPtr t = stackPtr s
  rsi : t.regValue .rsi = s.regValue .rsi
  registers : RegistersAt t (Reference.compress hash (Standards.NIST.SHA2.bytesToBits block))
  agrees : AgreesExcept (blockComponents s) s t
  statePointer : memLoad t.external (stackPtr t + 0xc0) 64 =
    memLoad s.external (stackPtr s + 0xc0) 64
  endPointer : memLoad t.external (stackPtr t + 0xc8) 64 =
    memLoad s.external (stackPtr s + 0xc8) 64

def BlockCorrect [Bindings] : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (hash : Array UInt32) (block : ByteArray),
    ReadyToStep s → ProgramLoaded s → ¬ InProgram boundary.rip →
    BlockPre s hash block → ∃ t, BlockResult s t boundary hash block

end P256.Proofs.SHA256.Compression
