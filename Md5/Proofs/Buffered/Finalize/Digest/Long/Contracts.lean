import Md5.Proofs.Buffered.Finalize.Algebra
import Md5.Proofs.Buffered.Finalize.Geometry

namespace Md5.Proofs.Buffered.Finalize.Digest.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def changes (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (stackPtr s - 320) 320, .mem (stackPtr s + 8) 168]

theorem agrees_digest {s t : RamState} (h : AgreesExcept (changes s) s t) :
    AgreesExcept (Kind.digest.changes s) s t := by
  apply h.mono
  intro c hc
  simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Kind.changes, Kind.localChanges]

structure Pre [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s : RamState) : Prop extends Storage .digest s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  boundaryOutside : ¬ InProgram boundary.rip
  rip : s.RIP = 0x10012a
  long : 56 ≤ message.size % 64
  input : (⟨(stackPtr s + 24).toNat, 64⟩ : MemoryRegion).HasBytes s.external
    (firstBlock message)
  buffer : (⟨(stackPtr s + 8).toNat, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(absorbedBuffer message).toBytes.toArray⟩
  position : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)
  blocks : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)

structure Post [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x1001df
  storage : Storage .digest t
  rsp : stackPtr t = stackPtr s
  zeroPrefix : Bytes t.external (stackPtr t + 24) 56 (fun _ ↦ 0)
  buffer : (⟨(stackPtr t + 8).toNat, 16⟩ : MemoryRegion).HasBytes t.external
    ⟨(Standards.RFC.MD5.processBlocks (absorbedBuffer message)
      (Standards.RFC.MD5.wordsOfBytes (firstBlock message))).toBytes.toArray⟩
  position : (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64)
  blocks : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64)
  agrees : AgreesExcept (Kind.digest.changes s) s t

end Md5.Proofs.Buffered.Finalize.Digest.Long
