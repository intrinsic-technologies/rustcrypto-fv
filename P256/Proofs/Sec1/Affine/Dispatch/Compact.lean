import P256.Proofs.Sec1.Affine.Dispatch.Mask
import P256.Proofs.Common.Instructions.ByteOps.Effects

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

theorem compact_route [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {tag : UInt8} (pre : AffineDecodePre s boundary bytes)
    (state : Routed s t tag) (rip : t.RIP = 0x110207) :
    ∃ u, Advances boundary 2 t u ∧ Routed s u tag ∧
      u.RIP = (if tag = 5 then 0x11020f else 0x110635) := by
  obtain ⟨a, runA, readyA, ea⟩ := (cmp_al_imm8_effect_step 0x110207 5).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x10207
      [0x3c,5] (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10209 (by decide)))
  change (cmpAlImm8Effect 0x110207 5 t).Holds t a at ea
  have agA : AgreesExcept [.flags,.rip] t a := ea.agrees
  have sa := state.toFrameState.after_registers readyA agA (by simp [Component.Covers]) (by simp)
  have al : (Operand.reg 0 : Operand 8).read t = tag.toBitVec := by
    change (t.regValue .rax).setWidth 8 = _
    rw [state.tagRegister, BitVec.setWidth_setWidth_of_le _ (by decide)]
    rfl
  have zf := ea.flags.2.2.2.1
  change (StatusFlags.ofRFLAGS a.RFLAGS).ZF =
    (cmpSpec ((Operand.reg 0 : Operand 8).read t) 5).ZF at zf
  rw [al] at zf
  have tags : ∀ tag : BitVec 8, (!(cmpSpec tag 5).ZF) = (!(tag == 5)) := by
    decide +kernel
  have condition : condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS) = (!(tag == 5)) := by
    change (!(StatusFlags.ofRFLAGS a.RFLAGS).ZF) = _
    rw [zf, tags]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h
      cases tag
      cases h
      rfl
    · rintro rfl
      rfl
  obtain ⟨u, step, ready, eu⟩ := jcc_rel32_effect_step 0x110209 5 0x426 a readyA
    (programText_slice (programLoaded_codeIn sa.loaded) 0x10209
      [0x0f,0x85,0x26,4,0,0] (by decide) (by decide +kernel))
    ⟨ea.rip, fun _ => by decide⟩
  have next : u.RIP = (if tag = 5 then 0x11020f else 0x110635) := by
    rw [eu.rip]
    change (if condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS) then
      (0x110635 : BitVec 64) else 0x11020f) = _
    rw [condition]
    by_cases ht : tag = 5 <;> simp [ht]
  have agU : AgreesExcept [.rip] a u := eu.agrees
  have total := agA.trans agU
  refine ⟨u, runA.trans (Advances.of_step step (.inl ?_)),
    ⟨sa.after_registers ready agU (by simp [Component.Covers]) (by simp),
      (total.read (n := 64) (r := 3) (by simp)).trans state.output,
      (total.read (n := 64) (r := 6) (by simp)).trans state.input,
      (total.read (n := 64) (r := 14) (by simp)).trans state.xPointer,
      (total.read (n := 64) (r := 0) (by simp)).trans state.tagRegister⟩, next⟩
  rw [next]
  split
  · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1020f (by decide))
  · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10635 (by decide))

end P256.Proofs.Sec1.Affine
