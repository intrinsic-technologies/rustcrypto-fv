import Md5.Proofs.Buffered.Invariant
import Md5.Proofs.Block.Frame

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive UpdateKind where
  | slices
  | resetFirst
  | resetSecond
  | updateFinalizeInto
  | finalizeResetFirst
  | finalizeResetSecond
  | resetDiscardFirst
  | resetDiscardSecond
  deriving DecidableEq

namespace UpdateKind

def entry : UpdateKind → BitVec 64
  | .slices => 0x100355
  | .resetFirst => 0x1006d0
  | .resetSecond => 0x1009df
  | .updateFinalizeInto => 0x101905
  | .finalizeResetFirst => 0x100d80
  | .finalizeResetSecond => 0x10106f
  | .resetDiscardFirst => 0x10140a
  | .resetDiscardSecond => 0x101549

def exits : UpdateKind → List (BitVec 64)
  | .slices => [0x100331, 0x10040f]
  | .resetFirst => [0x1006ac, 0x10076b]
  | .resetSecond => [0x1009b6, 0x100a6f]
  | .updateFinalizeInto => [0x1018e1, 0x1019bf]
  | .finalizeResetFirst => [0x100d5c, 0x100e1b]
  | .finalizeResetSecond => [0x101046, 0x1010ff]
  | .resetDiscardFirst => [0x1013ec, 0x1014a6]
  | .resetDiscardSecond => [0x101529, 0x1015df]

def contextOffset : UpdateKind → Nat
  | .slices => 192
  | .resetFirst | .resetSecond => 8
  | .updateFinalizeInto => 192
  | .finalizeResetFirst => 8
  | .finalizeResetSecond => 8
  | .resetDiscardFirst => 32
  | .resetDiscardSecond => 32

def inputRegister : UpdateKind → BitVec 5
  | .slices => 14
  | .resetFirst => 12
  | .resetSecond => 6
  | .updateFinalizeInto => 14
  | .finalizeResetFirst => 12
  | .finalizeResetSecond => 6
  | .resetDiscardFirst => 3
  | .resetDiscardSecond => 3

def sizeRegister : UpdateKind → BitVec 5
  | .slices => 3
  | .resetFirst => 14
  | .resetSecond => 12
  | .updateFinalizeInto => 3
  | .finalizeResetFirst => 14
  | .finalizeResetSecond => 12
  | .resetDiscardFirst => 14
  | .resetDiscardSecond => 13

def workRegisters : UpdateKind → List (BitVec 5)
  | .slices => [3, 5, 13, 14]
  | .resetFirst => [3, 12, 13, 14]
  | .resetSecond => [12, 13, 14]
  | .updateFinalizeInto => [3, 5, 13, 14]
  | .finalizeResetFirst => [3, 12, 13, 14]
  | .finalizeResetSecond => [12, 13, 14]
  | .resetDiscardFirst => [3, 5, 13, 14]
  | .resetDiscardSecond => [3, 5, 13, 14]

def context (kind : UpdateKind) (s : RamState) : BitVec 64 :=
  stackPtr s + BitVec.ofNat 64 kind.contextOffset

def inputRegion (kind : UpdateKind) (s : RamState) (input : ByteArray) : MemoryRegion :=
  ⟨((Operand.reg kind.inputRegister : Operand 64).read s).toNat, input.size⟩

def contextRegion (kind : UpdateKind) (s : RamState) : MemoryRegion :=
  ⟨(kind.context s).toNat, 88⟩

def scratchRegion (s : RamState) : MemoryRegion :=
  ⟨(stackPtr s).toNat - 320, 320⟩

def changes (kind : UpdateKind) (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip] ++ kind.workRegisters.map Component.reg ++
  [.mem (BitVec.ofNat 64 (scratchRegion s).start) 320, .mem (kind.context s) 88]

end UpdateKind

structure UpdatePre [bindings : Bindings] (kind : UpdateKind) (boundary : ReturnBoundary)
    (message input : ByteArray) (s : RamState) : Prop where
  stride : UnitStringStride bindings
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  df : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  rip : s.RIP = kind.entry
  boundaryOutside : ¬ InProgram boundary.rip
  absorbed : Absorbed (kind.context s) message s
  inputBytes : (kind.inputRegion s input).HasBytes s.external input
  inputBounded : (kind.inputRegion s input).Bounded
  inputSize : (Operand.reg kind.sizeRegister : Operand 64).read s =
    BitVec.ofNat 64 input.size
  totalSize : message.size + input.size < 2^64
  stackLow : 320 ≤ (stackPtr s).toNat
  stackHigh : (stackPtr s).toNat + kind.contextOffset + 88 < userAddressLimit
  stackAligned : (stackPtr s).toNat % 16 = 0
  scratchAllocated : (UpdateKind.scratchRegion s).Allocated s.external
  contextAllocated : (kind.contextRegion s).Allocated s.external
  inputScratch : (kind.inputRegion s input).Disjoint (UpdateKind.scratchRegion s)
  inputContext : (kind.inputRegion s input).Disjoint (kind.contextRegion s)
  scratchAvoids : (UpdateKind.scratchRegion s).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)
  contextAvoids : (kind.contextRegion s).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)
  secondRegisters : (kind = .resetSecond ∨ kind = .finalizeResetSecond) →
    (Operand.reg 3 : Operand 64).read s = kind.context s ∧
    (Operand.reg 15 : Operand 64).read s = 0x1024b0
  discardSecondMemcpy : kind = .resetDiscardSecond →
    (Operand.reg 15 : Operand 64).read s = 0x1024b0

structure UpdatePost [Bindings] (kind : UpdateKind) (boundary : ReturnBoundary)
    (message input : ByteArray) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP ∈ kind.exits
  absorbed : Absorbed (kind.context s) (message ++ input) t
  agrees : AgreesExcept (kind.changes s) s t

theorem UpdatePost.rsp [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s t : RamState}
    (h : UpdatePost kind boundary message input s t) : stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  cases kind <;> simp [UpdateKind.changes, UpdateKind.workRegisters]

theorem UpdatePost.preservedRegister [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {s t : RamState}
    (h : UpdatePost kind boundary message input s t) {r : BitVec 5}
    (hr : Component.reg r ∉ kind.changes s) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s :=
  h.agrees.read hr

theorem UpdateKind.frame {kind : UpdateKind} {s t : RamState}
    (h : AgreesExcept (kind.changes s) s t)
    (hScratch : (UpdateKind.scratchRegion s).Bounded)
    (hContext : (kind.contextRegion s).Bounded) :
    MemoryWriteFrame s t #v[UpdateKind.scratchRegion s, kind.contextRegion s] := by
  apply h.memoryWriteFrame
  intro c hc address hcover
  simp only [UpdateKind.changes, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with (hc | hc) | hc
  · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hcover.elim
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hc
    exact hcover.elim
  · rcases hc with rfl | rfl
    · exact ⟨UpdateKind.scratchRegion s, by simp,
        Block.contains_of_mem_covers hScratch hcover⟩
    · refine ⟨kind.contextRegion s, by simp, ?_⟩
      apply Block.contains_of_mem_covers hContext
      simpa only [UpdateKind.contextRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hcover

theorem UpdatePost.frame [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s t : RamState}
    (h : UpdatePost kind boundary message input s t)
    (hScratch : (UpdateKind.scratchRegion s).Bounded)
    (hContext : (kind.contextRegion s).Bounded) :
    MemoryWriteFrame s t #v[UpdateKind.scratchRegion s, kind.contextRegion s] :=
  UpdateKind.frame h.agrees hScratch hContext

end Md5.Proofs.Buffered
