import Hkdf.Proofs.Standard.Memory
import Hkdf.Proofs.Common.Machine.Boundary

set_option autoImplicit false

namespace Hkdf.Proofs.Standard

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame

theorem buffer_frame_agrees {initial s t : RamState}
    (frame : MemoryWriteFrame s t #v[(⟨(hmacBase initial).toNat, 64⟩ : MemoryRegion)])
    {offset size : Nat} (small : size + 64 < 2^64)
    (apart : OffsetsApart (-BitVec.ofNat 64 offset) size (-400) 64) :
    (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) size).Agrees s t := by
  have pointer : hmacBase initial = stackPtr initial - 400 := by
    change stackPtr initial - 520 + 120 = stackPtr initial - 400
    bv_omega
  intro i hi
  apply frame _
  intro region member cover
  have eq : region = (⟨(hmacBase initial).toNat, 64⟩ : MemoryRegion) := by simpa using member
  subst region
  rw [pointer] at cover
  have cover' : (Component.mem (stackPtr initial - 400) 64).Covers
      (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
    have result := Hkdf.Proofs.Common.Machine.mem_covers_of_contains cover
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using result
  obtain ⟨j, hj, eq⟩ := cover'
  apply OffsetsApart.ne apart (stackPtr initial) hi hj small
  simpa only [BitVec.sub_eq_add_neg] using eq

theorem Preserved.of_buffer_frame [Bindings] {initial s t : RamState}
    (state : Preserved initial s)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] t)
    (frame : MemoryWriteFrame s t #v[(⟨(hmacBase initial).toNat, 64⟩ : MemoryRegion)])
    (rsp : t.regValue .rsp = frameBase initial) : Preserved initial t := by
  have saved := buffer_frame_agrees frame (offset := 48) (size := 56)
    (by decide) (by unfold OffsetsApart; decide +kernel)
  apply state.of_observations running saved _ rsp
  intro offset member
  have bound : offset ≤ 112 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have equal : frameBase initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
    have e := stack_address state.rsp (offset := offset) (by omega)
    simpa only [show rspOf s = frameBase initial from state.rsp] using e
  rw [equal]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exact buffer_frame_agrees frame (by decide) (by unfold OffsetsApart; decide +kernel)

end Hkdf.Proofs.Standard
