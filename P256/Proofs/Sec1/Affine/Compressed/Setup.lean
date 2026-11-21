import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Encoding.Parser.CompressedRoute.Movzx
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.ByteOps.ByteOps
open P256.Proofs.Common.Encoding.Parser.CompressedRoute

theorem parity_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {tag : UInt8} (pre : AffineDecodePre s boundary bytes) (state : Routed s t tag)
    (rip : t.RIP = 0x110108) :
    ∃ u, Advances boundary 2 t u ∧ Frame s u ∧ u.RIP = 0x11010d ∧
      u.regValue .rdi = (tag.toBitVec &&& 1).setWidth 64 ∧
      AgreesExcept [.reg 0, .reg 7, .flags, .rip] t u := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (and_al_imm8_effect_step 0x110108 1).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x10108 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1010a (by decide)))
  change (andAlImm8Effect 0x110108 1 t).Holds t a at effectA
  have frameA := state.toFrameState.after_registers readyA effectA.agrees
    (by simp [andAlImm8Effect_components, Component.Covers]) (by simp [andAlImm8Effect_components])
  obtain ⟨u, runU, readyU, effectU⟩ :=
    (movzx_r32_al_effect_step 0x11010a 0xf8 rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn frameA.loaded) 0x1010a _
        (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1010d (by decide)))
  change (movzxAlEffect 0x11010a 7 a).Holds a u at effectU
  have agreesU : AgreesExcept [.reg 7, .rip] a u := effectU.agrees
  refine ⟨u, runA.trans runU, frameA.after_registers readyU agreesU
    (by simp [Component.Covers]) (by simp), effectU.rip, ?_,
    (effectA.agrees.trans agreesU).mono (by simp [andAlImm8Effect_components])⟩
  have ax : (Operand.reg 0 : Operand 8).read a = tag.toBitVec &&& 1 := by
    change ((Operand.reg 0 : Operand 64).read a).setWidth 8 = _
    rw [effectA.writes, mergeGPR_low8]
    change ((t.regValue .rax).setWidth 8 &&& 1) = _
    rw [state.tagRegister, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
    rfl
  exact effectU.writes.trans (congrArg (BitVec.setWidth 64) ax)

theorem choice [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (offset : Nat) (disp : BitVec 32) (bound : offset + 5 < 118431)
    (bytesAt : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 6 t u ∧ Frame s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 offset + (5 : BitVec 64) ∧
      u.regValue .rax = ((t.regValue .rdi).setWidth 8).setWidth 64 ∧
      AgreesExcept (ScalarFrame.choiceClobbers s 760) t u := by
  obtain ⟨u, run, ready, sp, ip, ax, agrees⟩ := ScalarFrame.choice_step pre.toCalleePre
    (frameOffset := 760) (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated state.rsp
    offset disp bound bytesAt target rip
  have narrow : AgreesExcept [.reg 0, .flags, .rip,
      .mem (stackPtr s - 768) 8, .mem (stackPtr s - 769) 1] t u := by
    apply agrees.narrow
    intro c hc hn
    simp only [ScalarFrame.choiceClobbers, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0, .flags, .rip,
      .mem (stackPtr s - 768) 8, .mem (stackPtr s - 769) 1]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 3360] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals exact ⟨ScalarFrame.workRegion s 3360, by simp,
      ScalarFrame.work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  exact ⟨u, run, state.after_effect pre.toCalleePre (by decide) ready narrow writes
    (by simp), ip, ax, agrees⟩

end P256.Proofs.Sec1.Affine.Compressed
