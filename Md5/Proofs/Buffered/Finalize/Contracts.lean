import Md5.Proofs.Buffered.Invariant
import Md5.Proofs.Block.Frame

namespace Md5.Proofs.Buffered.Finalize

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive Kind where
  | digest
  | slices
  | resetSecond
  | finalizeResetSecond
  | resetDiscardSecond
  | updateFinalizeInto
  deriving DecidableEq

namespace Kind

def entry : Kind → BitVec 64
  | .digest => 0x1000cf
  | .slices => 0x10042b
  | .resetSecond => 0x100a90
  | .finalizeResetSecond => 0x101120
  | .resetDiscardSecond => 0x1015fd
  | .updateFinalizeInto => 0x1019db

def exit : Kind → BitVec 64
  | .digest => 0x100260
  | .slices => 0x1005b9
  | .resetSecond => 0x100c68
  | .finalizeResetSecond => 0x1012f8
  | .resetDiscardSecond => 0x1017f9
  | .updateFinalizeInto => 0x101b69

def contextOffset : Kind → Nat
  | .digest => 176
  | .slices | .updateFinalizeInto => 192
  | .resetSecond | .finalizeResetSecond => 8
  | .resetDiscardSecond => 32

def resultOffset : Kind → Nat
  | .digest => 8
  | .slices | .updateFinalizeInto => 0
  | .resetSecond | .finalizeResetSecond => 216
  | .resetDiscardSecond => 120

def stackBytes : Kind → Nat
  | .digest => 264
  | .slices | .updateFinalizeInto => 280
  | .resetSecond | .finalizeResetSecond => 296
  | .resetDiscardSecond => 288

def context (kind : Kind) (s : RamState) : BitVec 64 :=
  stackPtr s + BitVec.ofNat 64 kind.contextOffset

def resultRegion (kind : Kind) (s : RamState) : MemoryRegion :=
  ⟨(stackPtr s).toNat + kind.resultOffset, 16⟩

def stackRegion (kind : Kind) (s : RamState) : MemoryRegion :=
  ⟨(stackPtr s).toNat - 320, 320 + kind.stackBytes⟩

def localChanges (kind : Kind) (s : RamState) : List Component :=
  match kind with
  | .digest => [.mem (stackPtr s + 8) 168]
  | .slices | .updateFinalizeInto => [.mem (stackPtr s) 168]
  | .resetSecond | .finalizeResetSecond => [.mem (stackPtr s + 96) 88, .mem (stackPtr s + 216) 80]
  | .resetDiscardSecond => [.mem (stackPtr s + 120) 168]

def workRegisters : Kind → List (BitVec 5)
  | .digest => [12, 14, 15]
  | .slices | .resetSecond | .finalizeResetSecond | .resetDiscardSecond | .updateFinalizeInto =>
    [3, 14, 15]

def changes (kind : Kind) (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (stackPtr s - 320) 320] ++
  kind.workRegisters.map Component.reg ++ kind.localChanges s

end Kind

structure Storage (kind : Kind) (s : RamState) : Prop where
  stackLow : 320 ≤ (stackPtr s).toNat
  stackHigh : (stackPtr s).toNat + kind.stackBytes < userAddressLimit
  stackAligned : (stackPtr s).toNat % 16 = 0
  stackAllocated : (kind.stackRegion s).Allocated s.external
  stackAvoids : (kind.stackRegion s).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)

theorem Storage.of_agrees {kind : Kind} {s t : RamState} {cs : List Component}
    (h : Storage kind s) (ha : AgreesExcept cs s t) (hsp : stackPtr t = stackPtr s) :
    Storage kind t := by
  have hr : kind.stackRegion t = kind.stackRegion s := by
    exact congrArg (fun rsp : BitVec 64 ↦
      (⟨rsp.toNat - 320, 320 + kind.stackBytes⟩ : MemoryRegion)) hsp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hsp] using h.stackLow
  · simpa only [hsp] using h.stackHigh
  · simpa only [hsp] using h.stackAligned
  · rw [hr]
    intro a ha'
    exact Option.isSome_iff_exists.mp
      (ha.grow a (Option.isSome_iff_exists.mpr (h.stackAllocated a ha')))
  · rw [hr]
    exact h.stackAvoids

structure Pre [bindings : Bindings] (kind : Kind) (boundary : ReturnBoundary)
    (message : ByteArray) (s : RamState) : Prop extends Storage kind s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  stride : UnitStringStride bindings
  df : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  rip : s.RIP = kind.entry
  boundaryOutside : ¬ InProgram boundary.rip
  absorbed : Absorbed (kind.context s) message s
  messageBounded : message.size < 2^64
  digestState : kind = .digest →
    (Operand.reg 14 : Operand 64).read s = stackPtr s + 240

structure Post [Bindings] (kind : Kind) (boundary : ReturnBoundary)
    (message : ByteArray) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = kind.exit
  digest : (kind.resultRegion s).HasBytes t.external
    ⟨(Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes message)).toArray⟩
  agrees : AgreesExcept (kind.changes s) s t

theorem Post.rsp [Bindings] {kind : Kind} {boundary : ReturnBoundary}
    {message : ByteArray} {s t : RamState} (h : Post kind boundary message s t) :
    stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  cases kind <;> simp [Kind.changes, Kind.workRegisters, Kind.localChanges]

theorem Post.preservedRegister [Bindings] {kind : Kind} {boundary : ReturnBoundary}
    {message : ByteArray} {s t : RamState} (h : Post kind boundary message s t)
    {r : BitVec 5} (hr : Component.reg r ∉ kind.changes s) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s :=
  h.agrees.read hr

end Md5.Proofs.Buffered.Finalize
