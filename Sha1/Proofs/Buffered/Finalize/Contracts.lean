import Sha1.Proofs.Buffered.Invariant
import X86Proofs.Program.Execution

namespace Sha1.Proofs.Buffered.Finalize

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.NIST Standards.NIST.SHA1 Standards.NIST.SHA2

inductive Kind where
  | digestCopy
  | finalizeFixedResetFirst
  | finalizeFixedResetSecond
  | finalizeIntoResetFirst
  | finalizeIntoResetSecond
  | finalizeResetFirst
  | finalizeResetSecond
  | resetCopy
  | updateFinalizeCopy
  | updateResetCopy
  deriving DecidableEq

namespace Kind

def frameBytes : Nat := 344

def entry : Kind → BitVec 64
  | .digestCopy => 0x1000da
  | .finalizeFixedResetFirst => 0x100479
  | .finalizeFixedResetSecond => 0x10079d
  | .finalizeIntoResetFirst => 0x100b29
  | .finalizeIntoResetSecond => 0x100e3d
  | .finalizeResetFirst => 0x1011ba
  | .finalizeResetSecond => 0x1014c8
  | .resetCopy => 0x1019dd
  | .updateFinalizeCopy => 0x101dcb
  | .updateResetCopy => 0x10229d

def exit : Kind → BitVec 64
  | .digestCopy => 0x100277
  | .finalizeFixedResetFirst => 0x100665
  | .finalizeFixedResetSecond => 0x100954
  | .finalizeIntoResetFirst => 0x100cdf
  | .finalizeIntoResetSecond => 0x100ff4
  | .finalizeResetFirst => 0x1013c8
  | .finalizeResetSecond => 0x1016f2
  | .resetCopy => 0x101c13
  | .updateFinalizeCopy => 0x101fb9
  | .updateResetCopy => 0x1024ce

def contextOffset : Kind → Nat
  | .digestCopy => 0xb8
  | .finalizeFixedResetFirst | .finalizeFixedResetSecond => 0x18
  | .finalizeIntoResetFirst | .finalizeIntoResetSecond => 0x18
  | .finalizeResetFirst => 0
  | .finalizeResetSecond => 0x78
  | .resetCopy => 0x90
  | .updateFinalizeCopy => 0xd8
  | .updateResetCopy => 0x90

def outputRegister : Kind → BitVec 5
  | .digestCopy => 3
  | .updateFinalizeCopy => 1
  | _ => 8

def stackBytes : Kind → Nat
  | .digestCopy => 0x118
  | .finalizeFixedResetFirst | .finalizeFixedResetSecond => 608
  | .finalizeIntoResetFirst | .finalizeIntoResetSecond => 608
  | .finalizeResetFirst | .finalizeResetSecond | .resetCopy | .updateResetCopy => 704
  | .updateFinalizeCopy => 0x138

def context (kind : Kind) (s : RamState) : BitVec 64 :=
  stackPtr s + BitVec.ofNat 64 kind.contextOffset

def resultRegion (kind : Kind) (s : RamState) : MemoryRegion :=
  match kind with
  | .digestCopy => ⟨(stackPtr s).toNat, 20⟩
  | .updateFinalizeCopy =>
      ⟨((Operand.mem (stackPtr s + 0xc0) : Operand 64).read s).toNat, 20⟩
  | _ => ⟨(Operand.reg kind.outputRegister : Operand 64).read s |>.toNat, 20⟩

def resultBytes (kind : Kind) (message : ByteArray) : ByteArray :=
  match kind with
  | .digestCopy =>
      ⟨(Hasher.stateBytes
        (SHA1.hashComputation (SHA2.SHA256.parse (SHA2.SHA256.pad (SHA2.bytesToBits message))))).toArray⟩
  | _ => ⟨(SHA1.SHA1 (SHA2.bytesToBits message)).bytes.toArray⟩

def stackRegion (kind : Kind) (s : RamState) : MemoryRegion :=
  ⟨(stackPtr s).toNat - frameBytes, frameBytes + kind.stackBytes⟩

def localChanges (kind : Kind) (s : RamState) : List Component :=
  [.mem (stackPtr s - frameBytes) (frameBytes + kind.stackBytes)]

def workRegisters : Kind → List (BitVec 5)
  | .digestCopy => [12, 14, 15]
  | _ => [3, 14, 15]

def changes (kind : Kind) (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
    .reg 11, .flags, .rip] ++ kind.workRegisters.map Component.reg ++ kind.localChanges s ++
    match kind with
    | .updateFinalizeCopy =>
        [.mem ((Operand.mem (stackPtr s + 0xc0) : Operand 64).read s) 20]
    | _ => []

end Kind

structure Storage (kind : Kind) (s : RamState) : Prop where
  stackLow : Kind.frameBytes ≤ (stackPtr s).toNat
  stackHigh : (stackPtr s).toNat + kind.stackBytes < userAddressLimit
  stackAligned : (stackPtr s).toNat % 16 = 0
  stackAllocated : (kind.stackRegion s).Allocated s.external
  stackAvoids : (kind.stackRegion s).Avoids
    (fun address ↦ InProgram address ∨ InPageTables address)

structure Pre [bindings : Bindings] (kind : Kind) (boundary : ReturnBoundary)
    (message : ByteArray) (s : RamState) : Prop extends Storage kind s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  stride : UnitStringStride bindings
  df : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  rip : s.RIP = kind.entry
  boundaryOutside : ¬ InProgram boundary.rip
  absorbed : Absorbed (kind.context s) message s
  messageBounded : message.size < 2 ^ 64

structure Post [Bindings] (kind : Kind) (boundary : ReturnBoundary)
    (message : ByteArray) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = kind.exit
  digest : (kind.resultRegion s).HasBytes t.external
    (kind.resultBytes message)
  agrees : AgreesExcept (kind.changes s) s t

theorem Storage.of_agrees {kind : Kind} {s t : RamState} {cs : List Component}
    (h : Storage kind s) (ha : AgreesExcept cs s t) (hsp : stackPtr t = stackPtr s) :
    Storage kind t := by
  have hr : kind.stackRegion t = kind.stackRegion s := by
    exact congrArg (fun rsp : BitVec 64 ↦
      (⟨rsp.toNat - Kind.frameBytes, Kind.frameBytes + kind.stackBytes⟩ : MemoryRegion)) hsp
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

theorem Post.rsp [Bindings] {kind : Kind} {boundary : ReturnBoundary}
    {message : ByteArray} {s t : RamState} (h : Post kind boundary message s t) :
    stackPtr t = stackPtr s := by
  apply h.agrees.read (n := 64) (r := 4)
  cases kind <;> simp [Kind.changes, Kind.localChanges, Kind.workRegisters]

theorem Post.preservedRegister [Bindings] {kind : Kind} {boundary : ReturnBoundary}
    {message : ByteArray} {s t : RamState} (h : Post kind boundary message s t)
    {r : BitVec 5} (hr : Component.reg r ∉ kind.changes s) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s :=
  h.agrees.read hr

end Sha1.Proofs.Buffered.Finalize
