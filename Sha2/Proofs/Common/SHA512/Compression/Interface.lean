import Sha2.Proofs.Common.SHA512.State
import Sha2.Proofs.Common.Machine.StackFrame

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def blockComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7,
    .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
    .rip, .flags, .mem (stackPtr s) 224, .mem (stackPtr s + BitVec.ofNat 64 240) 128]

structure BlockPre (s : RamState) (hash : Array UInt64) (block : ByteArray) : Prop where
  stack : Common.Machine.StackFramePre 0x10ddf0 14940 0 416 s
  registers : RegistersAt s hash
  inputReadable : MemReadable s (s.regValue .rsi) 128
  inputBytes : (registerRegion s .rsi 128).HasBytes s.external block
  inputSeparate : RangeApart (s.regValue .rsi) 128 (stackPtr s) 416
  frameAvoids : ∀ i < 416, ¬ InProgram (stackPtr s + BitVec.ofNat 64 i)

structure BlockResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt64) (block : ByteArray) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  rip : t.RIP = 0x111802
  rsp : stackPtr t = stackPtr s
  rsi : t.regValue .rsi = s.regValue .rsi
  registers : RegistersAt t (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits block))
  agrees : AgreesExcept (blockComponents s) s t
  statePointer : memLoad t.external (stackPtr t + 0xe0) 64 =
    memLoad s.external (stackPtr s + 0xe0) 64
  endPointer : memLoad t.external (stackPtr t + 0xe8) 64 =
    memLoad s.external (stackPtr s + 0xe8) 64

def BlockCorrect [Bindings] : Prop :=
  ∀ (s : RamState) (boundary : ReturnBoundary) (hash : Array UInt64) (block : ByteArray),
    ReadyToStep s → ProgramLoaded s → ¬ InProgram boundary.rip →
    BlockPre s hash block → ∃ t, BlockResult s t boundary hash block

end Sha2.Proofs.Common.SHA512.Compression
