import Sha3.Proofs.Permutation.Call
import Sha3.Proofs.Memory
import Sha3.Proofs.Image
import X86Proofs.Instructions.Call.Form

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

structure CallPre (copy : Copy) (s : RamState) : Prop where
  rip : s.RIP = entryAddress copy
  stack : Stack.Valid s frameBytes
  stackAvoid : (Stack.region s frameBytes).Avoids fun address ↦
    InProgram address ∨ InPageTables address
  dataRead : MemReadable s (s.regValue .rdi) 200
  apart : RangeApart (s.regValue .rdi) 200 (frameBase s) 272
  dataAvoid : ∀ i, i < 200 → ¬ (InProgram (s.regValue .rdi + BitVec.ofNat 64 i) ∨
    InPageTables (s.regValue .rdi + BitVec.ofNat 64 i))
  target : InProgram (stackTop s)

theorem CallPre.frameRegion {copy : Copy} {s : RamState} (h : CallPre copy s) :
    Stack.region s frameBytes = ⟨(frameBase s).toNat, 272⟩ := by
  have hbase : (frameBase s).toNat = (s.regValue .rsp).toNat - 264 :=
    stack_sub_toNat h.stack.2.2.1 (Nat.le_refl frameBytes)
  rw [hbase]
  change (⟨(s.regValue .rsp).toNat - 264,
    (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 264)⟩ : MemoryRegion) = _
  have hbottom : 264 ≤ (s.regValue .rsp).toNat := h.stack.2.2.1
  have hsize : (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 264) = 272 := by omega
  rw [hsize]

theorem CallPre.frameRead {copy : Copy} {s : RamState} (h : CallPre copy s) :
    MemReadable s (frameBase s) 272 := by
  have hb := h.stack.1
  have ha := h.stack.2.1
  rw [h.frameRegion] at hb ha
  exact memReadable_of_region hb ha (Nat.le_refl _) (Nat.le_refl _)

theorem CallPre.frameContains {copy : Copy} {s : RamState} (h : CallPre copy s) {i : Nat} (hi : i < 272) :
    (Stack.region s frameBytes).Contains (frameBase s + BitVec.ofNat 64 i).toNat := by
  have hl := h.frameRead.low
  rw [h.frameRegion]
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> omega

theorem CallPre.frameAvoid {copy : Copy} {s : RamState} (h : CallPre copy s) {i : Nat} (hi : i < 272) :
    ¬ (InProgram (frameBase s + BitVec.ofNat 64 i) ∨
      InPageTables (frameBase s + BitVec.ofNat 64 i)) :=
  h.stackAvoid _ (h.frameContains hi)

theorem CallPre.targetLow {copy : Copy} {s : RamState} (h : CallPre copy s) :
    (stackTop s).toNat < 2^32 := by
  obtain ⟨byte, hb⟩ := h.target
  exact (SectionsLow.codeLow programSections_low) (stackTop s, byte) hb

theorem CallPre.return_ne_boundary {copy : Copy} {s : RamState} {boundary : ReturnBoundary}
    (h : CallPre copy s) (hb : ¬ InProgram boundary.rip) : stackTop s ≠ boundary.rip := by
  intro he
  exact hb (he ▸ h.target)

theorem CallPre.frameRead_of_frame {copy : Copy} {initial s : RamState} (h : CallPre copy initial)
    (hf : CallFrame initial s) : MemReadable s (frameBase initial) 272 :=
  hf.readable h.frameRead

theorem CallPre.dataRead_of_frame {copy : Copy} {initial s : RamState} (h : CallPre copy initial)
    (hf : CallFrame initial s) : MemReadable s (initial.regValue .rdi) 200 :=
  hf.readable h.dataRead

end Sha3.Proofs.Permutation
