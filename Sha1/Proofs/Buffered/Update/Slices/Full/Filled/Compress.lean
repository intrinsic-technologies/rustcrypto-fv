import Sha1.Proofs.Buffered.Update.Slices.Full.Filled.CopyEntry
import Sha1.Proofs.Buffered.Update.Slices.Full.Filled.Resume
import Sha1.Proofs.Buffered.Update.Slices.Full.Compress
import Sha1.Proofs.Buffered.Update.Slices.Counter
import Sha1.Proofs.Buffered.Update.Slices.CompressionFrame
import Sha1.Proofs.Buffered.Update.Slices.FilledBlock
import Sha1.Proofs.Compress.Machine.Execution
import Sha1.Proofs.MemoryRoutines.Register.Compose

namespace Sha1.Proofs.Buffered.Update.Slices.Full.Filled

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine (AdvancesBlock program_text_slice)
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return)
open Sha1.Proofs.Wrapper.Absorb (filledBlock filledBlock_size)

private def setupBytes : List UInt8 :=
  [0xba, 1, 0, 0, 0, 0x48, 0x8d, 0xbc, 0x24, 0x20, 1, 0, 0,
    0x48, 0x8d, 0xb4, 0x24, 0xd8, 0, 0, 0]

private def setupEffect (s : RamState) : Effect where
  rip := 0x101d4c
  writes := [⟨(.reg 2 : Operand 64), 1⟩, ⟨(.reg 7 : Operand 64), stackPtr s + 288⟩,
    ⟨(.reg 6 : Operand 64), stackPtr s + 216⟩]

private theorem setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101d37)
      (codeRange 0x101d37 setupBytes) setupEffect := by
  unfold setupBytes
  md5_run_begin mov_r32_imm32_effect_step 0x101d37 0xba (by decide) 1
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d3c (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x101d3c 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d32 288)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d37) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d44 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x101d44 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d32 216)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101d37) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hout 0x1d4c (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [setupEffect]
  · x86_norm [setupEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [setupEffect, stackPtr]
    all_goals rfl
  · x86_norm [setupEffect]

set_option maxRecDepth 2048 in
theorem compress_copied [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre .updateFinalize boundary message input s)
    (b : CopyEntry boundary message input s u) (hsize : 64 - message.size % 64 ≤ input.size) :
    ∃ v, AfterCompress boundary message input s v := by
  let base := UpdateKind.updateFinalize.context s
  let block := filledBlock message input
  have hblock : block.size = 64 := filledBlock_size message input hsize
  have hsp : stackPtr u = stackPtr s := b.agrees.read (n := 64) (r := 4) (by decide)
  have hext := b.agrees.external (by simp [Component.Covers])
  have hu : AgreesExcept (UpdateKind.updateFinalize.changes s) s u := b.agrees.mono
    (by simp [UpdateKind.changes, UpdateKind.workRegisters])
  have hfit : message.size % 64 + (64 - message.size % 64) ≤ 64 := by omega
  obtain ⟨v, hc⟩ := copy_input (src := 0) h b.agrees hsp b.ready b.code
    (b.agrees.directionFlagClear (by decide) ⟨h.df⟩).df b.rip (.inr (.inl rfl))
    (by rw [b.src]; exact (BitVec.add_zero _).symm) b.dst b.len (by simpa using hsize) hfit
  obtain ⟨hb, hh, hn⟩ := buffer_after_copy h hext hsp b.dst b.src b.len hsize hfit hc
  have hv := (hu.trans (copy_agrees h hc hsp b.dst b.len (by omega))).mono
    (cs' := UpdateKind.updateFinalize.changes s) (by simp)
  obtain ⟨w, inc, wr, wc, wip, wa, wn⟩ := inc_counter hc.ready hc.code h.boundaryOutside hc.rip
    (counter_writable h hv)
  have vw := counter_agrees (stack_same hv) wa
  have hw := (hv.trans vw).mono (cs' := UpdateKind.updateFinalize.changes s) (by simp)
  rw [stack_same hv, counter_address] at wa wn
  change AgreesExcept [.mem (base + 64) 8, .flags, .rip] v w at wa
  have hbw : (⟨base.toNat, block.size⟩ : MemoryRegion).HasBytes w.external block := by
    have hzero : base + BitVec.ofNat 64 0 = base := BitVec.add_zero _
    have hb' : (⟨(base + BitVec.ofNat 64 0).toNat, block.size⟩ : MemoryRegion).HasBytes v.external block := by
      rw [hzero]
      exact hb
    simpa only [hzero] using
      counter_preserves_bytes (off := 0) wa hb' (by rw [hblock]; decide) (by rw [hblock]; decide)
  have hhw := counter_preserves_bytes (off := 72) (len := 20) wa hh (by decide) (by decide)
  have codeArgs : CodeIn (codeRange 0x101d37 setupBytes) w := program_text_slice wc 0x1d37 21 (by decide +kernel)
  obtain ⟨nf, y, args, yr, _, ye⟩ := setup boundary h.boundaryOutside w wr codeArgs wip
  have ya : AgreesExcept [.reg 2, .reg 7, .reg 6, .rip] w y := ye.agrees
  have hy := (hw.trans ya).mono (cs' := UpdateKind.updateFinalize.changes s)
    (by simp [UpdateKind.changes, UpdateKind.workRegisters])
  have yext := ya.external (by simp [Component.Covers])
  have ycode := ya.codeIn (by simp [Component.Covers]) wc
  have ydx : y.regValue .rdx = 1 := ye.writes.1
  have ydi : y.regValue .rdi = base + 72 := by
    change (Operand.reg 7 : Operand 64).read y = _
    rw [ye.writes.2.1, stack_same hw]
    change stackPtr s + 288 = (stackPtr s + 216) + 72
    rw [BitVec.add_assoc]
    rfl
  have ysi : y.regValue .rsi = base := by
    change (Operand.reg 6 : Operand 64).read y = _
    rw [ye.writes.2.2, stack_same hw]
    rfl
  have yb : (Sha1.Spec.Program.Compress.inputRegion y block).HasBytes y.external block := by
    change (⟨(y.regValue .rsi).toNat, block.size⟩ : MemoryRegion).HasBytes y.external block
    rw [ysi, yext]
    exact hbw
  obtain ⟨t, ht⟩ := Full.compress (hash := absorbedHash message) h hy (stack_same hy) yr ycode
    (hy.directionFlagClear (by simp [UpdateKind.changes, UpdateKind.workRegisters]) ⟨h.df⟩).df
    (show y.RIP = 0x101d4c from ye.rip) (.inl rfl) ydi (by rw [ydx, hblock]; decide)
    (.inl ⟨ysi, hblock⟩) yb (by rw [yext]; exact hhw)
  obtain ⟨nu, au⟩ := b.advances
  obtain ⟨nv, av⟩ := hc.advances
  obtain ⟨nt, at'⟩ := ht.advances
  have regs (r : BitVec 5) (hr : r = 3 ∨ r = 5) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read u := by
    rcases hr with rfl | rfl <;>
      exact (ht.agrees.read (by simp [compressChanges])).trans
        ((ya.read (by decide)).trans ((wa.read (by simp)).trans (hc.agrees.read (by simp [callSiteChanges]))))
  refine ⟨t, ⟨⟨_, (((au.trans av).trans inc).trans args).trans at'⟩, ht.ready, ht.code, ht.rip,
    (hy.trans (compression_agrees ht.agrees)).mono (by simp), (regs 3 (.inl rfl)).trans b.next,
    (regs 5 (.inr rfl)).trans b.remaining, ?_, ?_⟩⟩
  · rw [absorbedStateBytes, absorbedHash_append_fill_prefix _ _ hsize]
    exact ht.state
  · rw [counter_preserved h.stackLow h.stackHigh ht.agrees]
    change memLoad y.external (base + 64) 64 = _
    rw [yext]
    exact wn.trans (by rw [hn, BitVec.ofNat_add]; rfl)

end Sha1.Proofs.Buffered.Update.Slices.Full.Filled
