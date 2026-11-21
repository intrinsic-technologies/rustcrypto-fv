import P256.Proofs.Sec1.Affine.Dispatch.Range
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.And.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.R8Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem mask_route [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (state : Tagged s t (bytes.data[0]?.getD 0)) (rip : t.RIP = 0x1100f6) :
    ∃ u, Advances boundary 5 t u ∧ Routed s u (bytes.data[0]?.getD 0) ∧
      u.RIP = (if bytes.data[0]?.getD 0 = 2 ∨ bytes.data[0]?.getD 0 = 3 then
        0x110108 else 0x110207) := by
  obtain ⟨a, runA, readyA, ea⟩ :=
    (lea_r64_effect_step 0x1100f6 0x4c (by simp [RexWPrefix]) 6 (.base 6 (.d8 1))
      (by decide) rfl rfl).advances (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x100f6
        [0x4c,0x8d,0x76,1] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x100fa (by decide)))
  change (leaR64Effect 0x1100f6 14 (.base 6 (.d8 1)) t).Holds t a at ea
  have sa := state.toFrameState.after_registers readyA ea.agrees (by simp [Component.Covers]) (by simp)
  obtain ⟨b, runB, readyB, eb⟩ :=
    (mov_r32_r32_effect_step 0x1100fa 0xc1 rfl).advances readyA
      (programText_slice (programLoaded_codeIn sa.loaded) 0x100fa
        [0x89,0xc1] (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x100fc (by decide)))
  change (movR32R32Effect 0x1100fa 2 1 0 a).Holds a b at eb
  have sb := sa.after_registers readyB eb.agrees (by simp [Component.Covers]) (by simp)
  obtain ⟨c, runC, readyC, ec⟩ :=
    (and_r8_imm8_effect_step 0x1100fc 0xe1 6 rfl rfl (by decide)).advances readyB
      (programText_slice (programLoaded_codeIn sb.loaded) 0x100fc
        [0x80,0xe1,6] (by decide) (by decide +kernel)) eb.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x100ff (by decide)))
  change (andR8Imm8Effect 0x1100fc 3 1 6 b).Holds b c at ec
  have sc := sb.after_registers readyC ec.agrees (by simp [Component.Covers]) (by simp)
  obtain ⟨d, runD, readyD, ed⟩ :=
    (cmp_r8_imm8_effect_step 0x1100ff 0xf9 2 rfl rfl (by decide)).advances readyC
      (programText_slice (programLoaded_codeIn sc.loaded) 0x100ff
        [0x80,0xf9,2] (by decide) (by decide +kernel)) ec.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10102 (by decide)))
  change (cmpR8Imm8Effect 0x1100ff 3 1 2 c).Holds c d at ed
  have sd := sc.after_registers readyD ed.agrees (by simp [Component.Covers]) (by simp)
  have ax : a.regValue .rax = (bytes.data[0]?.getD 0).toBitVec.setWidth 64 :=
    (ea.agrees.read (n := 64) (r := 0) (by simp)).trans state.tagRegister
  have cl : (Operand.reg 1 : Operand 8).read c = (bytes.data[0]?.getD 0).toBitVec &&& 6 := by
    change ((Operand.reg 1 : Operand 64).read c).setWidth 8 = _
    rw [ec.writes, setWidth_mergeGPR8]
    change ((b.regValue .rcx).setWidth 8 &&& 6) = _
    have bx : b.regValue .rcx = ((a.regValue .rax).setWidth 32).setWidth 64 := eb.writes
    rw [bx, ax]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  have zf := ed.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS d.RFLAGS).ZF =
    (cmpSpec ((Operand.reg 1 : Operand 8).read c) 2).ZF at zf
  rw [cl] at zf
  have condition : condHolds 5 (StatusFlags.ofRFLAGS d.RFLAGS) =
      (!(bytes.data[0]?.getD 0 == 2 || bytes.data[0]?.getD 0 == 3)) := by
    change (!(StatusFlags.ofRFLAGS d.RFLAGS).ZF) = _
    rw [zf]
    rcases encoding_tag_cases pre.input.1 with hz | h2 | h3 | h4 | h5
    all_goals first | (rw [hz]; decide +kernel) | (rw [h2]; decide +kernel) |
      (rw [h3]; decide +kernel) | (rw [h4]; decide +kernel) | (rw [h5]; decide +kernel)
  obtain ⟨u, step, ready, eu⟩ := jcc_rel32_effect_step 0x110102 5 0xff d readyD
    (programText_slice (programLoaded_codeIn sd.loaded) 0x10102
      [0x0f,0x85,0xff,0,0,0] (by decide) (by decide +kernel))
    ⟨ed.rip, fun _ => by decide⟩
  have next : u.RIP = (if bytes.data[0]?.getD 0 = 2 ∨ bytes.data[0]?.getD 0 = 3 then
      0x110108 else 0x110207) := by
    rw [eu.rip]
    change (if condHolds 5 (StatusFlags.ofRFLAGS d.RFLAGS) then
      (0x110207 : BitVec 64) else 0x110108) = _
    rw [condition]
    rcases encoding_tag_cases pre.input.1 with hz | h2 | h3 | h4 | h5
    all_goals first | simp [hz] | simp [h2] | simp [h3] | simp [h4] | simp [h5]
  have euA : AgreesExcept [.rip] d u := eu.agrees
  have after := ((eb.agrees.trans ec.agrees).trans ed.agrees).trans euA
  have total := ea.agrees.trans after
  refine ⟨u, (((runA.trans runB).trans runC).trans runD).trans
    (Advances.of_step step (.inl ?_)),
    ⟨sd.after_registers ready euA (by simp [Component.Covers]) (by simp),
      (total.read (n := 64) (r := 3) (by simp)).trans state.output,
      (total.read (n := 64) (r := 6) (by simp)).trans state.input, ?_,
      (total.read (n := 64) (r := 0) (by simp)).trans state.tagRegister⟩, next⟩
  · rw [next]
    split
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10108 (by decide))
    · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10207 (by decide))
  · have ptr : a.regValue .r14 = t.regValue .rsi + 1 := ea.writes
    exact (after.read (n := 64) (r := 14) (by simp)).trans
      (ptr.trans (congrArg (· + 1) state.input))

end P256.Proofs.Sec1.Affine
