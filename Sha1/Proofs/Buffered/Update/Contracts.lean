import Sha1.Proofs.Buffered.Invariant

namespace Sha1.Proofs.Buffered

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive UpdateKind where
  | digest
  | finalizeFixedReset
  | finalizeIntoReset
  | finalizeReset
  | reset
  | updateFinalize
  | updateReset
  deriving DecidableEq

namespace UpdateKind

def entry : UpdateKind → BitVec 64
  | .digest => 0x100072
  | .finalizeFixedReset => 0x100318
  | .finalizeIntoReset => 0x100a38
  | .finalizeReset => 0x1010d4
  | .reset => 0x1017a0
  | .updateFinalize => 0x101cf5
  | .updateReset => 0x102088

def exits : UpdateKind → List (BitVec 64)
  | .digest => [0x1000da]
  | .finalizeFixedReset => [0x100463, 0x100783]
  | .finalizeIntoReset => [0x100b13, 0x100e27]
  | .finalizeReset => [0x1011a4, 0x1014c8]
  | .reset => [0x101897, 0x1019dd]
  | .updateFinalize => [0x101cd1, 0x101daf]
  | .updateReset => [0x10229d]

def contextOffset : UpdateKind → Nat
  | .digest | .finalizeFixedReset | .finalizeIntoReset => 0x18
  | .finalizeReset => 0
  | .reset => 0x30
  | .updateFinalize => 0xd8
  | .updateReset => 0x30

def inputRegister : UpdateKind → BitVec 5
  | .digest | .finalizeFixedReset | .finalizeIntoReset | .finalizeReset => 12
  | .reset | .updateReset => 3
  | .updateFinalize => 14

def sizeRegister : UpdateKind → BitVec 5
  | .digest | .finalizeFixedReset | .finalizeIntoReset | .finalizeReset => 15
  | .reset | .updateReset => 14
  | .updateFinalize => 3

def workRegisters : UpdateKind → List (BitVec 5)
  | .digest | .finalizeFixedReset | .finalizeIntoReset | .finalizeReset => [3, 12, 14, 15]
  | .reset | .updateReset => [3, 12, 13, 14, 15]
  | .updateFinalize => [3, 5, 13, 14]

def context (kind : UpdateKind) (s : RamState) : BitVec 64 :=
  stackPtr s + BitVec.ofNat 64 kind.contextOffset

def inputRegion (kind : UpdateKind) (s : RamState) (input : ByteArray) : MemoryRegion :=
  ⟨((Operand.reg kind.inputRegister : Operand 64).read s).toNat, input.size⟩

def contextRegion (kind : UpdateKind) (s : RamState) : MemoryRegion :=
  ⟨(kind.context s).toNat, 92⟩

def scratchRegion (s : RamState) : MemoryRegion :=
  ⟨(stackPtr s).toNat - 320, 320⟩

def changes (kind : UpdateKind) (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip] ++ kind.workRegisters.map Component.reg ++
    match kind with
    | .updateFinalize =>
        [.mem (kind.context s) 92, .mem (BitVec.ofNat 64 ((stackPtr s).toNat - 344)) 344]
    | _ => [.mem (BitVec.ofNat 64 (scratchRegion s).start) 320]

end UpdateKind

structure UpdatePre [bindings : Bindings] (kind : UpdateKind) (boundary : ReturnBoundary)
    (message input : ByteArray) (s : RamState) : Prop where
  stride : UnitStringStride bindings
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  df : DirectionFlagClear s.RFLAGS
  rip : s.RIP = kind.entry
  boundaryOutside : ¬ InProgram boundary.rip
  absorbed : Absorbed (kind.context s) message s
  inputBytes : (kind.inputRegion s input).HasBytes s.external input
  inputSize : (Operand.reg kind.sizeRegister : Operand 64).read s = BitVec.ofNat 64 input.size
  totalSize : message.size + input.size < 2^64
  inputBounded : (kind.inputRegion s input).Bounded
  stackLow : 344 ≤ (stackPtr s).toNat
  stackHigh : (stackPtr s).toNat + 0xd8 + 92 < userAddressLimit
  stackAligned : (stackPtr s).toNat % 16 = 0
  scratchAllocated : (⟨(stackPtr s).toNat - 344, 344⟩ : MemoryRegion).Allocated s.external
  contextAllocated : (kind.contextRegion s).Allocated s.external
  inputScratch : (kind.inputRegion s input).Disjoint
    (⟨(stackPtr s).toNat - 344, 344⟩ : MemoryRegion)
  inputContext : (kind.inputRegion s input).Disjoint (kind.contextRegion s)
  scratchAvoids : (⟨(stackPtr s).toNat - 344, 344⟩ : MemoryRegion).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)
  contextAvoids : (kind.contextRegion s).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)

structure UpdatePost [Bindings] (kind : UpdateKind) (boundary : ReturnBoundary)
    (message input : ByteArray) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP ∈ kind.exits
  absorbed : Absorbed (kind.context s) (message ++ input) t
  agrees : AgreesExcept (kind.changes s) s t

end Sha1.Proofs.Buffered
