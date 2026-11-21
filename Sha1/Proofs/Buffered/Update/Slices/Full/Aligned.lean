import Sha1.Proofs.Buffered.Update.Slices.Full.Contracts
import Sha1.Proofs.Buffered.DigestPrepare.Geometry
import Sha1.Proofs.Compress.Machine.Execution
import X86Proofs.Instructions.Branch.Triple

namespace Sha1.Proofs.Buffered.Update.Slices.Full

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine (AdvancesBlock program_text_slice)
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return)

theorem position_branch [Bindings] {boundary : ReturnBoundary} {u : RamState}
    (hReady : ReadyToStep u) (hCode : CodeIn Extracted.programImage u)
    (hRip : u.RIP = 0x101d0e) (hOutside : ¬ InProgram boundary.rip) :
    ∃ v, Advances boundary 2 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      v.RIP = (if (Operand.reg 13 : Operand 64).read u = 0 then 0x101dbd else 0x101d17) ∧
      AgreesExcept [.flags, .rip] u v := by
  have testBytes : CodeIn (codeRange 0x101d0e [0x4d, 0x85, 0xed]) u :=
    program_text_slice hCode 0x1d0e 3 (by decide +kernel)
  have test : StepEffect (fun s ↦ s.RIP = 0x101d0e)
      (codeRange 0x101d0e [0x4d, 0x85, 0xed]) (testR64R64Effect 0x101d0e 13 13) :=
    test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨w, hTest, wReady, testEffect⟩ := test.advances hReady testBytes hRip
    (text_address_ne_return hOutside 0x1d11 (by decide +kernel))
  have wCode := testEffect.codeIn (testR64R64Effect_avoids _ _ _ _ _) hCode
  have hZero : condHolds 4 (StatusFlags.ofRFLAGS w.RFLAGS) =
      ((Operand.reg 13 : Operand 64).read u == 0) := by
    have hz := testEffect.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS w.RFLAGS).ZF =
      (((Operand.reg 13 : Operand 64).read u &&& (Operand.reg 13 : Operand 64).read u) == 0) at hz
    change (StatusFlags.ofRFLAGS w.RFLAGS).ZF = _
    simpa only [BitVec.and_self] using hz
  have hNext : (jccEffect 0x101d11 6 4 ((0xa6#32).signExtend 64) w).rip =
      if (Operand.reg 13 : Operand 64).read u = 0 then 0x101dbd else 0x101d17 := by
    simp only [jccEffect, hZero, branchEffect, beq_iff_eq]
    split <;> rfl
  have hNextOutside : (jccEffect 0x101d11 6 4 ((0xa6#32).signExtend 64) w).rip ≠ boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return hOutside 0x1dbd (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1d17 (by decide +kernel)
  have branchBytes : CodeIn (codeRange 0x101d11 [0x0f, 0x84, 0xa6, 0, 0, 0]) w :=
    program_text_slice wCode 0x1d11 6 (by decide +kernel)
  obtain ⟨v, hBranch, vReady, branchPost⟩ := (jcc_rel32_effect_step 0x101d11 4 0xa6).advances
    wReady branchBytes ⟨testEffect.rip, fun _ ↦ by decide +kernel⟩ hNextOutside
  refine ⟨v, hTest.trans hBranch, vReady, branchPost.codeIn (branchEffect_avoids _ _ _ _) wCode,
    branchPost.rip.trans hNext, ?_⟩
  apply (testEffect.agrees.trans branchPost.agrees).mono
  simp [testR64R64Effect_components, jccEffect]

private def countBytes : List UInt8 :=
  [0x48, 0x89, 0xdd, 0x48, 0x89, 0xea, 0x48, 0xc1, 0xea, 0x06]

private def countEffect (s : RamState) : Effect where
  rip := 0x101dc7
  writes := [⟨(.reg 5 : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
    ⟨(.reg 2 : Operand 64), (Operand.reg 3 : Operand 64).read s >>> 6⟩]
  flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((Operand.reg 3 : Operand 64).read s))

private theorem count_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) : AdvancesBlock boundary (fun s ↦ s.RIP = 0x101dbd)
      (codeRange 0x101dbd countBytes) countEffect := by
  unfold countBytes
  md5_run_begin mov_r64_r64_effect_step 0x101dbd 0x48 0xdd
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1dc0 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101dc0 0x48 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101dbd) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1dc3 (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x101dc3 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101dbd) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1dc7 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [countEffect, shiftCount]
  · x86_norm [countEffect, shiftCount]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [countEffect, shiftCount] <;> rfl
  · x86_norm [countEffect, shiftCount] <;> rfl

theorem aligned [Bindings] {boundary : ReturnBoundary} {message input : ByteArray} {s u : RamState}
    (h : UpdatePre .updateFinalize boundary message input s)
    (b : BranchState boundary message input s u)
    (hsize : 64 - message.size % 64 ≤ input.size) (hpos : message.size % 64 = 0) :
    ∃ v, BatchReady boundary message input s 0 v := by
  have hRip : u.RIP = 0x101d0e := b.rip.trans (ite_eq_right (Nat.not_lt.mpr hsize))
  obtain ⟨w, hPosition, wReady, wCode, wRip, hPositionAgrees⟩ :=
    position_branch (boundary := boundary) b.ready b.code hRip h.boundaryOutside
  rw [b.position, hpos] at wRip
  have countBytesIn : CodeIn (codeRange 0x101dbd countBytes) w :=
    program_text_slice wCode 0x1dbd 10 (by decide +kernel)
  obtain ⟨fuel, t, hCount, tReady, _, ht⟩ := count_prepare boundary h.boundaryOutside
    w wReady countBytesIn wRip
  have hBeforeCount := b.agrees.trans hPositionAgrees
  have hInputSize : (Operand.reg 3 : Operand 64).read w = BitVec.ofNat 64 input.size :=
    (hBeforeCount.read (by decide)).trans h.inputSize
  have hSizeBound : input.size < 2^64 := by have := h.totalSize; omega
  have hBlockCount : (Operand.reg 3 : Operand 64).read w >>> 6 =
      BitVec.ofNat 64 (input.size / 64) := by
    rw [hInputSize]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hSizeBound]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have hNonzero : input.size / 64 ≠ 0 := by omega
  have hQuotBound : input.size / 64 < 2^64 := by omega
  have hBitNonzero : BitVec.ofNat 64 (input.size / 64) ≠ 0 := by
    intro he
    have hn := congrArg (fun x : BitVec 64 ↦ x.toNat) he
    change (BitVec.ofNat 64 (input.size / 64)).toNat = 0 at hn
    exact hNonzero (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQuotBound] using hn)
  have hCondition : condHolds 5 (StatusFlags.ofRFLAGS t.RFLAGS) = true := by
    have hz := ht.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      ((Operand.reg 3 : Operand 64).read w >>> 6 == 0) at hz
    change (!(StatusFlags.ofRFLAGS t.RFLAGS).ZF) = true
    rw [hz, hBlockCount, beq_eq_false_iff_ne.mpr hBitNonzero]
    rfl
  have tCode := ht.agrees.codeIn (by simp [countEffect, Effect.components, Component.Covers]) wCode
  have branchBytes : CodeIn (codeRange 0x101dc7 [0x75, 0x9c]) t :=
    program_text_slice tCode 0x1dc7 2 (by decide +kernel)
  have hNext : (jccEffect 0x101dc7 2 5 ((0x9c#8).signExtend 64) t).rip = 0x101d65 := by
    rw [jccEffect, hCondition]
    rfl
  have hNextOutside : (jccEffect 0x101dc7 2 5 ((0x9c#8).signExtend 64) t).rip ≠ boundary.rip := by
    rw [hNext]
    exact text_address_ne_return h.boundaryOutside 0x1d65 (by decide +kernel)
  obtain ⟨v, hBranch, vReady, hv⟩ := (jcc_rel8_effect_step 0x101dc7 5 0x9c).advances
    tReady branchBytes ⟨ht.rip, fun _ ↦ by decide +kernel⟩
    hNextOutside
  have hBranchAgrees : AgreesExcept [.rip] t v := hv.agrees
  have hCountAgrees : AgreesExcept [.reg 5, .reg 2, .flags, .rip] w t := ht.agrees
  have hAgrees := (hBeforeCount.trans hCountAgrees).trans hBranchAgrees
  have hMemory := hAgrees.external (by simp [Component.Covers])
  obtain ⟨entryFuel, hEntry⟩ := b.advances
  refine ⟨v, ⟨⟨⟨_, ((hEntry.trans hPosition).trans hCount).trans hBranch⟩, vReady,
    hv.codeIn (branchEffect_avoids _ _ _ _) tCode, ?_, Nat.zero_le _, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply hAgrees.mono
    simp [UpdateKind.changes, UpdateKind.workRegisters]
  · exact (hAgrees.read (n := 64) (r := 14) (by decide)).trans (BitVec.add_zero _).symm
  · simpa only [Nat.sub_zero] using
      (hBranchAgrees.read (n := 64) (r := 5) (by decide)).trans (ht.writes.1.trans hInputSize)
  · simpa only [Nat.sub_zero, hNonzero, ite_false] using hv.rip.trans hNext
  · simpa only [Nat.sub_zero] using
      (hBranchAgrees.read (n := 64) (r := 2) (by decide)).trans (ht.writes.2.trans hBlockCount)
  · simpa only [Nat.add_zero] using hpos
  · simpa only [hMemory, ByteArray.extract_same, ByteArray.append_empty]
      using h.absorbed.state
  · simpa only [Operand.read, hMemory, Nat.add_zero] using h.absorbed.blocks

end Sha1.Proofs.Buffered.Update.Slices.Full
