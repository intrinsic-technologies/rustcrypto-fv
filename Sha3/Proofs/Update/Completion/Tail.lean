import Sha3.Proofs.Update.Tail
import Sha3.Proofs.Update.FullBlocks.Context

namespace Sha3.Proofs.Update.Completion

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program
open Keccak Permutation

section Tail

variable [Bindings] {v : Variant} {initial s : RamState} {bytes : ByteArray}
    {state : Incremental.State} (hc : CallContext v initial bytes state)
    (h : BodyInvariant initial s) (boundary : ReturnBoundary) (hb : ¬ InProgram boundary.rip)

include hc h hb in
theorem tail_advance (offset full : Nat) (hspan : offset + full ≤ bytes.size)
    (hlt : bytes.size - (offset + full) < v.rate) (hip : s.RIP = tailAddress v)
    (hpointer : s.regValue .r15 = initial.regValue .rsi)
    (hslot : (Operand.mem (frameBase initial) : Operand 64).read s = initial.regValue .rsi + 200)
    (h14 : s.regValue .rbx = initial.regValue .rdx + BitVec.ofNat 64 offset)
    (h12 : s.regValue .r13 = BitVec.ofNat 64 full)
    (h15 : s.regValue .r12 = BitVec.ofNat 64 (bytes.size - (offset + full))) :
    ∃ fuel t, Advances boundary fuel s t ∧ BodyInvariant initial t ∧
      t.RIP = cursorWriteAddress v ∧
      t.regValue .rdi = initial.regValue .rsi + 200 ∧
      memoryLanes (initial.regValue .rsi) t =
        (Incremental.update keccakLanes v.rate
          ⟨memoryLanes (initial.regValue .rsi) s, 0⟩
          (bytes.extract (offset + full) bytes.size)).lanes ∧
      (Operand.reg 1 : Operand 64).read t = BitVec.ofNat 64
        (Incremental.update keccakLanes v.rate
          ⟨memoryLanes (initial.regValue .rsi) s, 0⟩
          (bytes.extract (offset + full) bytes.size)).cursor := by
  let tail := bytes.extract (offset + full) bytes.size
  let initialBytes := fun i ↦ memByte s.external (initial.regValue .rsi + BitVec.ofNat 64 i)
  have hsize : tail.size = bytes.size - (offset + full) := by
    simp only [tail, ByteArray.size_extract, Nat.min_self]
  have hctx : Tail.Context v (initial.regValue .rsi)
      (initial.regValue .rdx + BitVec.ofNat 64 offset) (BitVec.ofNat 64 full)
      tail.size initialBytes (fun i ↦ (tail.data[i]?).getD 0) s := by
    refine ⟨h.ready, CodeIn.of_loaded h.loaded (SectionsLow.codeLow programSections_low),
      hip, hpointer, h14, h12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsize]
      exact h15
    · exact h.cursorSlot_readable hc
    · simpa only [h.stack] using hslot
    · simpa only [hsize] using hlt
    · intro i hi
      have htotal : offset + full + i < bytes.size := by rw [hsize] at hi; omega
      have hin := FullBlocks.input_bytes hc h (offset + full + i)
        (by simpa only [Array.length_toList, ByteArray.size] using htotal)
      simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
      have hget : tail.data[i]? = some tail[i] := Array.getElem?_eq_getElem hi
      rw [hin, hget]
      simp only [Option.getD_some, Array.getElem_toList]
      congr 1
      change bytes[offset + full + i] = tail[i]
      exact (ByteArray.getElem_extract hi).symm
    · exact Bytes.of_isSome (fun i hi ↦ h.grows _ (hc.stateRead.mem i (by omega)))
    · have hl := hc.inputRead.low
      rw [hsize]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · have hl := hc.stateRead.low
      omega
    · intro i hi j hj he
      have hs := FullBlocks.state_contains hc (i := i) (by omega)
      have hj' : offset + full + j < bytes.size := by rw [hsize] at hj; omega
      have hr := FullBlocks.input_contains hc hj'
      have he' : initial.regValue .rsi + BitVec.ofNat 64 i =
          initial.regValue .rdx + BitVec.ofNat 64 (offset + full + j) := by
        simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_assoc] using he
      rw [he'] at hs
      exact hc.inputApart (stateRegion initial) (by simp [writeRegions]) _ hr hs
    · intro i hi
      exact hc.avoids (stateRegion initial) (by simp [writeRegions]) _
        (FullBlocks.state_contains hc (by omega))
  obtain ⟨fuel, t, ha, ht⟩ := Tail.advance hctx boundary hb
  have hupdate := ht.incremental hctx
  exact ⟨fuel, t, ha, ht.bodyInvariant hc h, ht.rip, ht.cursorReg, hupdate.1, hupdate.2⟩

end Tail

end Sha3.Proofs.Update.Completion
