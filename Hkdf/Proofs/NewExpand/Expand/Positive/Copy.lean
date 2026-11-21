import Hkdf.Proofs.NewExpand.Expand.Positive.Copy.Execution
import Hkdf.Proofs.NewExpand.Expand.Positive.Save

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine

theorem copyAndFinishRound [Bindings] {entry old s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (head : LoopState entry old boundary key info length n)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f53c)
    (more : 32*n < length) (bound : length ≤ 8160)
    (locals : ∀ i ∈ ([232, 240, 248, 416, 424, 440] : List (BitVec 64)), slot s i = slot old i)
    (copyPtr : s.regValue .r12 = 0x10dd60)
    (counter : slot s 256 = BitVec.ofNat 64 (n+1))
    (remaining : slot s 8 = BitVec.ofNat 64 (length - 32*(n+1)))
    (nextPtr : s.regValue .rbp = entry.regValue .rcx + BitVec.ofNat 64 (min (32*(n+1)) length))
    (dest : s.regValue .r14 = entry.regValue .rcx + BitVec.ofNat 64 (32*n))
    (src : s.regValue .r13 = stackPtr s + 16)
    (count : s.regValue .rbx = BitVec.ofNat 64 (min (length - 32*n) 32))
    (digest : (⟨(rspOf s + 16).toNat, 32⟩ : MemoryRegion).HasBytes s.external
      (blocks .sha256 key info (n+1)).2)
    (written : (registerRegion entry .rcx (min (32*n) length)).HasBytes s.external
      ((blocks .sha256 key info n).1.extract 0 length)) :
    ∃ t, LoopState entry t boundary key info length (n+1) := by
  obtain ⟨v,running,pcV,sp,abi,frame,chunk⟩ := copyChunk pre saved pc more bound copyPtr dest src count digest
  have bounds := stack_bounds pre.call.stack
  have spNat : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [show stackPtr s = stackPtr entry - 536 from saved.sp]
    exact stack_sub_toNat pre.call.stack (offset := 536) (by decide)
  have apart : (registerRegion entry .rcx length).Disjoint (Stack.region entry 2264) :=
    (pre.separation (by omega) bound).1 0 1 (by decide)
  have same : (Component.mem (stackPtr s) 544).Agrees s v := by
    apply frame_agrees_of_disjoint frame (by omega)
    intro region member a h
    change (stackPtr s).toNat ≤ a ∧ a < (stackPtr s).toNat + 544 at h
    have choices : region = outputChunk entry length n ∨ region = copyReturnSlot entry := by simpa using member
    rcases choices with rfl | rfl
    · intro ha
      apply apart a (outputChunk_within entry length n a ha)
      unfold MemoryRegion.Contains
      rw [stack_region_end]
      change (stackPtr entry).toNat - 2264 ≤ a ∧ _
      constructor <;> omega
    · change ¬ ((stackPtr entry).toNat - 544 ≤ a ∧ a < (stackPtr entry).toNat - 544 + 8)
      omega
  have fixed (i : Nat) (hi : i+8 ≤ 544) :
      slot v (BitVec.ofNat 64 i) = slot s (BitVec.ofNat 64 i) := by
    change memLoad v.external (stackPtr v + _) 64 = _
    rw [sp]
    exact agrees_memLoad_offset same hi
  have sameSaved : (Component.mem (stackPtr s + 488) 56).Agrees s v := by
    intro j hj
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, ← BitVec.add_assoc] using
      same (488+j) (by omega)
  have savedV := saved.of_agreement running sp sameSaved (fixed 224 (by decide)) abi.2.2.1 abi.2.2.2
  have fullFrame : MemoryWriteFrame s v #v[outputChunk entry length n, Stack.region entry 2264] := by
    apply frame_mono frame
    intro region member a ha
    have cases' : region = outputChunk entry length n ∨ region = copyReturnSlot entry := by simpa using member
    rcases cases' with rfl | rfl
    · exact ⟨outputChunk entry length n, by simp, ha⟩
    · exact ⟨Stack.region entry 2264, by simp, copyReturnSlot_within pre.call.stack ha⟩
  have digestV : (⟨(rspOf v + 16).toNat, 32⟩ : MemoryRegion).HasBytes v.external
      (blocks .sha256 key info (n+1)).2 := by
    change (⟨(stackPtr v + 16).toNat, 32⟩ : MemoryRegion).HasBytes _ _
    rw [sp]
    refine ⟨digest.1, fun i => ?_⟩
    have size : (blocks .sha256 key info (n+1)).2.size = 32 := digest.1
    have small : i.val < 32 := size ▸ i.isLt
    have eq := same (16+i.val) (by omega)
    change v.external[stackPtr s + BitVec.ofNat 64 (16+i.val)]? =
      s.external[stackPtr s + BitVec.ofNat 64 (16+i.val)]? at eq
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at eq
    have byte := digest.2 i
    change s.external[BitVec.ofNat 64 ((stackPtr s + 16).toNat + i.val)]? = _ at byte
    change v.external[BitVec.ofNat 64 ((stackPtr s + 16).toNat + i.val)]? = _
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte ⊢
    exact eq.trans byte
  apply finishRound pre head savedV pcV more bound _ ((abi.1 .r12 (by decide)).trans copyPtr)
    ((fixed 256 (by decide)).trans counter) ((fixed 8 (by decide)).trans remaining)
    ((abi.1 .rbp (by decide)).trans nextPtr) digestV (roundOutput pre written more bound fullFrame chunk)
  intro i hi
  have choices : i=232 ∨ i=240 ∨ i=248 ∨ i=416 ∨ i=424 ∨ i=440 := by simpa using hi
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (fixed 232 (by decide)).trans (locals _ hi)
  · exact (fixed 240 (by decide)).trans (locals _ hi)
  · exact (fixed 248 (by decide)).trans (locals _ hi)
  · exact (fixed 416 (by decide)).trans (locals _ hi)
  · exact (fixed 424 (by decide)).trans (locals _ hi)
  · exact (fixed 440 (by decide)).trans (locals _ hi)

end Hkdf.Proofs.NewExpand.Expand
