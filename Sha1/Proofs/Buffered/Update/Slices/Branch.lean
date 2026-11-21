import Sha1.Proofs.Buffered.Update.Slices.BranchState
import Sha1.Proofs.Buffered.Update.SlicesControl
import Sha1.Proofs.Buffered.DigestPrepare.Geometry
import Sha1.Proofs.Compress.Machine.Execution
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine (AdvancesBlock program_text_slice)
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return)

attribute [local x86_compose] movzxR32M8Effect

private def entryBytes : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0xac, 0x24, 0x17, 0x01, 0x00, 0x00,
    0xba, 0x40, 0x00, 0x00, 0x00, 0x4c, 0x29, 0xea, 0x48, 0x89, 0xdd,
    0x48, 0x29, 0xd5]

private def entryPosition (s : RamState) : BitVec 64 :=
  ((Operand.mem (stackPtr s + 0x117) : Operand 8).read s).setWidth 64

private def entryEffect (s : RamState) : Effect where
  rip := 0x101d0c
  writes := [⟨(.reg 13 : Operand 64), entryPosition s⟩,
    ⟨(.reg 2 : Operand 64), 64 - entryPosition s⟩,
    ⟨(.reg 5 : Operand 64), (Operand.reg 3 : Operand 64).read s - (64 - entryPosition s)⟩]
  flags := some (.ofStatusFlags
    (subSpec ((Operand.reg 3 : Operand 64).read s) (64 - entryPosition s)).2)

private theorem entry [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) : AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x101cf5 ∧ MemReadable s (stackPtr s + 0x117) 1)
      (codeRange 0x101cf5 entryBytes) entryEffect := by
  unfold entryBytes
  md5_run_begin movzx_r_m8_rex_effect_step 0x101cf5 0x44 (by unfold RexPrefix; decide)
    32 (.inr rfl) (fun _ ↦ rfl) 5 (.sib 4 none 0 (.d32 0x117))
    (by decide) (by decide) (by decide)
  case pre => intro s h; exact ⟨h.1, h.2⟩
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1cfe (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x101cfe 0xba (by decide) 64
  case sub => exact codeRange_mem_of_drop (p := 0x101cf5) 9 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1d03 (by decide +kernel)
  md5_run_then sub_r64_r64_effect_step 0x101d03 0x4c 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101cf5) 14 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1d06 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101d06 0x48 0xdd
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101cf5) 17 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1d09 (by decide +kernel)
  md5_run_then sub_r64_r64_effect_step 0x101d09 0x48 0xd5
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101cf5) 20 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1d0c (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [entryEffect]
  · x86_norm [entryEffect, entryPosition, stackPtr]
    exact ⟨rfl, rfl, rfl⟩
  · intro i; cases i <;> x86_norm [entryEffect, entryPosition, stackPtr]
    all_goals rfl
  · x86_norm [entryEffect]

private theorem entry_readable [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .updateFinalize boundary message input s) :
    MemReadable s (stackPtr s + 0x117) 1 := by
  have hHigh := h.stackHigh
  change (stackPtr s).toNat + 0xd8 + 92 < 2^32 at hHigh
  have hContext : (UpdateKind.updateFinalize.context s).toNat = (stackPtr s).toNat + 0xd8 :=
    toNat_add_ofNat (stackPtr s) 0xd8 (by omega)
  have hPosition : (stackPtr s + 0x117).toNat = (stackPtr s).toNat + 0x117 :=
    toNat_add_ofNat (stackPtr s) 0x117 (by omega)
  apply DigestPrepare.memReadable_of_allocated h.contextAllocated
  · rw [hPosition]
    omega
  · change (UpdateKind.updateFinalize.context s).toNat ≤ _
    rw [hContext, hPosition]
    omega
  · change _ ≤ (UpdateKind.updateFinalize.context s).toNat + 92
    rw [hContext, hPosition]
    omega

private theorem entry_position [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .updateFinalize boundary message input s) :
    entryPosition s = BitVec.ofNat 64 (message.size % 64) := by
  rw [entryPosition, position_eq h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

private theorem entry_gap (size : Nat) :
    (64 : BitVec 64) - BitVec.ofNat 64 (size % 64) = BitVec.ofNat 64 (64 - size % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat]
  omega

theorem branch [bindings : Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s : RamState} (h : UpdatePre .updateFinalize boundary message input s) :
    ∃ u, BranchState boundary message input s u := by
  have hEntryBytes : CodeIn (codeRange 0x101cf5 entryBytes) s :=
    program_text_slice h.code 0x1cf5 23 (by decide +kernel)
  obtain ⟨fuel, u, ha, hr, _, he⟩ := entry boundary h.boundaryOutside
    s h.ready hEntryBytes ⟨h.rip, entry_readable h⟩
  have hComponents : (entryEffect s).components = [.reg 13, .reg 2, .reg 5, .flags, .rip] := rfl
  have hCode : CodeIn Extracted.programImage u := by
    apply he.codeIn _ h.code
    apply Effect.Avoids.of_noMem
    rw [hComponents]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl | rfl | rfl) <;> intro x hx <;> exact hx
  have hPosition := entry_position h
  have hGap : (64 : BitVec 64) - entryPosition s = BitVec.ofNat 64 (64 - message.size % 64) :=
    congrArg (fun p => 64 - p) hPosition |>.trans (entry_gap message.size)
  have hSize : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 input.size := h.inputSize
  have hCarry : (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      decide (input.size < 64 - message.size % 64) := by
    have hcf := he.flags.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).CF =
      (subSpec ((Operand.reg 3 : Operand 64).read s) (64 - entryPosition s)).2.CF at hcf
    rw [hcf, hSize, hGap]
    simp only [subSpec, BitVec.toNat_ofNat]
    have hi := inputSize_lt h
    congr 1
    apply propext
    omega
  have hBranchBytes : CodeIn (codeRange 0x101d0c [0x72, 0xa2]) u :=
    program_text_slice hCode 0x1d0c 2 (by decide +kernel)
  have hNext : (jccEffect 0x101d0c 2 2 ((0xa2#8).signExtend 64) u).rip =
      (if input.size < 64 - message.size % 64 then 0x101cb0 else 0x101d0e) := by
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).CF = true then 0x101cb0 else 0x101d0e) = _
    rw [hCarry]
    simp only [decide_eq_true_eq]
  have hOutside : (jccEffect 0x101d0c 2 2 ((0xa2#8).signExtend 64) u).rip ≠ boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return h.boundaryOutside 0x1cb0 (by decide +kernel)
    · exact text_address_ne_return h.boundaryOutside 0x1d0e (by decide +kernel)
  obtain ⟨v, hb, hv, hbEffect⟩ := (jcc_rel8_effect_step 0x101d0c 2 0xa2).advances
    hr hBranchBytes ⟨he.rip, fun _ ↦ by decide +kernel⟩ hOutside
  have hAgrees : AgreesExcept [.rip] u v := hbEffect.agrees
  refine ⟨v, ⟨⟨fuel + 1, ha.trans hb⟩, hv,
    hbEffect.codeIn (branchEffect_avoids _ _ _ _) hCode, hbEffect.rip.trans hNext, ?_, ?_, ?_, ?_⟩⟩
  · rw [hAgrees.read (n := 64) (r := 13) (by decide)]
    exact he.writes.1.trans hPosition
  · rw [hAgrees.read (n := 64) (r := 2) (by decide)]
    exact he.writes.2.1.trans hGap
  · rw [hAgrees.read (n := 64) (r := 5) (by decide)]
    exact he.writes.2.2.trans (by rw [hSize, hGap])
  · apply (he.agrees.trans hAgrees).mono
    rw [hComponents]
    intro c hc
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, or_self] using hc

end Sha1.Proofs.Buffered.Update.Slices
