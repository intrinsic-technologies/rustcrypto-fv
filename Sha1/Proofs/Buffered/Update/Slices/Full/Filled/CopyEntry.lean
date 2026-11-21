import Sha1.Proofs.Buffered.Update.Slices.Full.Aligned
import Sha1.Proofs.Buffered.Update.Slices.Copy
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

namespace Sha1.Proofs.Buffered.Update.Slices.Full.Filled

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine (AdvancesBlock program_text_slice)
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return)

structure CopyEntry [Bindings] (boundary : ReturnBoundary) (message input : ByteArray)
    (s u : RamState) : Prop where
  advances : ∃ n, Advances boundary n s u
  ready : ReadyToStep u
  code : CodeIn Extracted.programImage u
  rip : u.RIP = 0x101d29
  agrees : AgreesExcept [.reg 13, .reg 2, .reg 5, .reg 3, .reg 7, .reg 6, .flags, .rip] s u
  dst : rdi.read u = UpdateKind.updateFinalize.context s + BitVec.ofNat 64 (message.size % 64)
  src : rsi.read u = (Operand.reg 14 : Operand 64).read s
  len : MemoryRoutines.rdx.read u = BitVec.ofNat 64 (64 - message.size % 64)
  next : (Operand.reg 3 : Operand 64).read u =
    (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 (64 - message.size % 64)
  remaining : (Operand.reg 5 : Operand 64).read u = BitVec.ofNat 64 (input.size - (64 - message.size % 64))

private def copySetupBytes : List UInt8 :=
  [0x49, 0x8d, 0x1c, 0x16, 0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x81, 0xc7,
    0xd8, 0, 0, 0, 0x4c, 0x89, 0xf6]

private def copySetupEffect (s : RamState) : Effect where
  rip := 0x101d29
  writes := [⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
    ⟨rdi, stackPtr s + (.reg 13 : Operand 64).read s + 216⟩,
    ⟨rsi, (.reg 14 : Operand 64).read s⟩]
  flags := some (.ofStatusFlags (addSpec (stackPtr s + (.reg 13 : Operand 64).read s) 216).2)

private theorem copy_setup [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) : AdvancesBlock boundary (fun s ↦ s.RIP = 0x101d17)
      (codeRange 0x101d17 copySetupBytes) copySetupEffect := by
  unfold copySetupBytes
  md5_run_begin lea_r64_effect_step 0x101d17 0x49 (by unfold RexWPrefix; decide)
    3 (.sib 14 (some 2) 0 .none) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d1b (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x101d1b 0x4a (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d17) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d1f (by decide +kernel)
  md5_run_then add_r64_imm32_effect_step 0x101d1f 0x48 0xc7 216
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d17) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d26 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101d26 0x4c 0xf6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d17) 15 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d29 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [copySetupEffect]
  · x86_norm [copySetupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
    rfl
  · intro i; cases i <;> x86_norm [copySetupEffect, BitVec.shiftLeft_zero, BitVec.add_zero]
  · x86_norm [copySetupEffect]

theorem copy_entry [Bindings] {boundary : ReturnBoundary} {message input : ByteArray} {s u : RamState}
    (h : UpdatePre .updateFinalize boundary message input s)
    (b : BranchState boundary message input s u)
    (hsize : 64 - message.size % 64 ≤ input.size) (hpos : message.size % 64 ≠ 0) :
    ∃ v, CopyEntry boundary message input s v := by
  have hRip : u.RIP = 0x101d0e := b.rip.trans (ite_eq_right (Nat.not_lt.mpr hsize))
  have hPosNonzero : BitVec.ofNat 64 (message.size % 64) ≠ 0 := by
    intro he
    have hn : (BitVec.ofNat 64 (message.size % 64)).toNat = 0 := congrArg BitVec.toNat he
    exact hpos (by simpa only [BitVec.toNat_ofNat, BitVec.toNat_zero,
      Nat.mod_eq_of_lt (by omega : message.size % 64 < 2^64)] using hn)
  obtain ⟨w, hPosition, wReady, wCode, wRip, hPositionAgrees⟩ :=
    position_branch (boundary := boundary) b.ready b.code hRip h.boundaryOutside
  rw [b.position, ite_eq_right hPosNonzero] at wRip
  have hBytes : CodeIn (codeRange 0x101d17 copySetupBytes) w :=
    program_text_slice wCode 0x1d17 18 (by decide +kernel)
  obtain ⟨_, v, hSetup, vReady, _, hv⟩ := copy_setup boundary h.boundaryOutside w wReady hBytes wRip
  have hBeforeSetup := b.agrees.trans hPositionAgrees
  have hSetupAgrees : AgreesExcept [.reg 3, .reg 7, .reg 6, .flags, .rip] w v := hv.agrees
  have hAgrees := hBeforeSetup.trans hSetupAgrees
  have hStack : stackPtr w = stackPtr s :=
    hBeforeSetup.read (n := 64) (r := 4) (by decide)
  have hInput : (Operand.reg 14 : Operand 64).read w = (Operand.reg 14 : Operand 64).read s :=
    hBeforeSetup.read (by decide)
  have hPositionReg : (Operand.reg 13 : Operand 64).read w = BitVec.ofNat 64 (message.size % 64) :=
    (hPositionAgrees.read (by decide)).trans b.position
  have hGap : (Operand.reg 2 : Operand 64).read w = BitVec.ofNat 64 (64 - message.size % 64) :=
    (hPositionAgrees.read (by decide)).trans b.gap
  obtain ⟨_, hEntry⟩ := b.advances
  refine ⟨v, ⟨⟨_, (hEntry.trans hPosition).trans hSetup⟩, vReady, ?_, hv.rip,
    hAgrees.mono (by decide), ?_, hv.writes.2.2.trans hInput, ?_, ?_, ?_⟩⟩
  · exact hv.codeIn (Effect.Avoids.of_noMem (by
      simp [copySetupEffect, rdi, rsi, Effect.components, Component.Covers]) _) wCode
  · change rdi.read v = (stackPtr s + 216) + BitVec.ofNat 64 (message.size % 64)
    rw [hv.writes.2.1, hStack, hPositionReg, BitVec.add_assoc, BitVec.add_assoc,
      BitVec.add_comm (BitVec.ofNat 64 (message.size % 64)) 216]
  · exact (hSetupAgrees.read (by decide)).trans hGap
  · change (Operand.reg 3 : Operand 64).read v = _
    rw [hv.writes.1, hInput, hGap]
  · exact (hSetupAgrees.read (by decide)).trans ((hPositionAgrees.read (by decide)).trans
      (b.remaining.trans (BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hsize)))

end Sha1.Proofs.Buffered.Update.Slices.Full.Filled
