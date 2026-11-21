import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.Finalize.Algebra

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive Variant where
  | original
  | finalize
  | discard
  deriving DecidableEq

def Variant.toKind : Variant → Kind
  | .original => .resetSecond
  | .finalize => .finalizeResetSecond
  | .discard => .resetDiscardSecond

def Variant.tailOffset : Variant → Nat
  | .original | .finalize => 96
  | .discard => 136

def Variant.resultOffset : Variant → Nat
  | .original | .finalize => 216
  | .discard => 120

def Variant.blockOffset : Variant → Nat
  | .original | .finalize => 232
  | .discard => 224

def Variant.preparedRip : Variant → BitVec 64
  | .original => 0x100aef
  | .finalize => 0x10117f
  | .discard => 0x101662

def Variant.paddedRip : Variant → BitVec 64
  | .original => 0x100bcf
  | .finalize => 0x10125f
  | .discard => 0x101757

def Variant.finalCall : Variant → BitVec 64
  | .original => 0x100c63
  | .finalize => 0x1012f3
  | .discard => 0x1017f4

structure Transition [Bindings] (boundary : ReturnBoundary) (s t : RamState)
    (variant : Variant := .original) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  agrees : AgreesExcept (variant.toKind.changes s) s t

theorem Transition.rsp [Bindings] {variant : Variant} {boundary : ReturnBoundary} {s t : RamState}
    (h : Transition boundary s t variant) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by
    cases variant <;> simp [Variant.toKind, Kind.changes, Kind.workRegisters, Kind.localChanges])

theorem Transition.trans [Bindings] {variant : Variant} {boundary : ReturnBoundary} {s t u : RamState}
    (h : Transition boundary s t variant) (h' : Transition boundary t u variant) :
    Transition boundary s u variant := by
  obtain ⟨n, hn⟩ := h.advances
  obtain ⟨m, hm⟩ := h'.advances
  refine ⟨⟨n + m, hn.trans hm⟩, ?_⟩
  have hc : variant.toKind.changes t = variant.toKind.changes s := by
    simp only [Kind.changes, Kind.localChanges, h.rsp]
  have ha := h'.agrees
  rw [hc] at ha
  apply (h.agrees.trans ha).mono
  intro c hc
  simpa only [List.mem_append, or_self] using hc

structure Prepared [Bindings] (message : ByteArray) (s : RamState)
    (variant : Variant := .original) : Prop
    extends Storage variant.toKind s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = variant.preparedRip
  first : Bytes s.external (stackPtr s + BitVec.ofNat 64 variant.tailOffset) 64 (fun i ↦ (firstBlock message)[i]!)
  buffer : (⟨(stackPtr s).toNat + variant.resultOffset, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(absorbedBuffer message).toBytes.toArray⟩
  blocks : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)
  position : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)
  remaining : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 (63 - message.size % 64)

structure Padded [Bindings] (message : ByteArray) (s : RamState)
    (variant : Variant := .original) : Prop
    extends Storage variant.toKind s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = variant.paddedRip
  prefixBytes : Bytes s.external (stackPtr s + BitVec.ofNat 64 variant.tailOffset) 56
    (fun i ↦ if message.size % 64 < 56 then (firstBlock message)[i]! else 0)
  buffer : (⟨(stackPtr s).toNat + variant.resultOffset, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(paddedBuffer message).toBytes.toArray⟩
  blocks : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)
  position : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond
