import P256.Proofs.HMAC.Key.Interface
import P256.Proofs.Program.State

set_option autoImplicit false

namespace P256.Proofs.HMAC.Key
open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def bufferAddress (s : RamState) : BitVec 64 := stackPtr s - 368

def bufferRegion (s : RamState) : MemoryRegion :=
  { start := (bufferAddress s).toNat, size := 64 }

def savedRegisters : List (Syntax.Reg × Nat) :=
  [(.r15, 8), (.r14, 16), (.r12, 24), (.rbx, 32)]

def stackComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6, .reg 7, .reg 8,
   .reg 12, .reg 14, .reg 15, .rip, .flags, .mem (stackPtr s - 384) 384]

structure CopyEntry [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (key : ByteArray) : Prop where
  pre : CalleePre t boundary 0x11c930 key.size key.size 0
  execution : ∃ fuel, Advances boundary fuel s t
  agrees : AgreesExcept (stackComponents s) s t
  rsp : stackPtr t = stackPtr s - 384
  source : t.regValue .rsi = s.regValue .rsi
  destination : t.regValue .rdi = bufferAddress s
  count : t.regValue .rdx = BitVec.ofNat 64 key.size
  output : t.regValue .rbx = s.regValue .rdi
  saved : ∀ entry ∈ savedRegisters,
    (Operand.mem (stackPtr s - BitVec.ofNat 64 entry.2) : Operand 64).read t =
      s.regValue entry.1
  returnAddress : (returnBoundary t).rip = 0x1293da
  zero : ∀ i < 64, t.external[bufferAddress s + BitVec.ofNat 64 i]? = some 0
  input : (registerRegion s .rsi key.size).HasBytes t.external key

structure CopiedEntry [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (key : ByteArray) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  agrees : AgreesExcept (stackComponents s) s t
  rip : t.RIP = 0x1293da
  rsp : stackPtr t = stackPtr s - 376
  output : t.regValue .rbx = s.regValue .rdi
  saved : ∀ entry ∈ savedRegisters,
    (Operand.mem (stackPtr s - BitVec.ofNat 64 entry.2) : Operand 64).read t =
      s.regValue entry.1
  buffer : (bufferRegion s).HasBytes t.external (keyPad key 0)

end P256.Proofs.HMAC.Key
