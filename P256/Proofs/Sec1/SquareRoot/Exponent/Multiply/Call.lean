import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply.State
import P256.Proofs.Sec1.SquareRoot.Exponent.CallPre
import P256.Proofs.Sec1.SquareRoot.Exponent.Memory
import P256.Proofs.Sec1.SquareRoot.Exponent.Finish.Memory
import P256.Proofs.Program.FieldCall.Binary
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentMultiply

open P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def callLayout : StackCallLayout 1584 32 32 160 :=
  ⟨1424, 1368, 1400, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem multiply_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x n d y : Nat}
    (ctx : ExponentPre s boundary x) (h : CallState s t x n d y) (hd : d < 16) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentPosition s u x n ∧
      u.RIP = 0x1158d2 ∧ Field.MontgomeryAt u (exponentFrameBase s + 0x10)
        (y * (x ^ d % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := by
  obtain ⟨v, run, ready, effect⟩ := scalar_call ctx.toCalleePre (by decide) (by decide)
    h.frame.scalarFrame 0x158c5 0xffffed16 (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x145e0 (by decide)) h.rip
  have frameV := h.frame.scalarFrame.after_call ctx.toCalleePre (by decide) (by decide) ready effect
  have left : v.regValue .rsi = stackPtr s - 1368 := by
    exact (effect.agrees.read (n := 64) (r := 6) (by simp)).trans
      (h.left.trans (ExponentTail.frame_address (off := 48) (by decide)))
  have right : v.regValue .rdx = stackPtr s - BitVec.ofNat 64 (592-32*d) := by
    have hv := (effect.agrees.read (n := 64) (r := 2) (by simp)).trans h.right
    change v.regValue .rdx = exponentFrameBase s + BitVec.ofNat 64 824 + BitVec.ofNat 64 (32*d) at hv
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at hv
    rw [ExponentTail.frame_address (by omega)] at hv
    simpa only [show 1416-(824+32*d) = 592-32*d by omega] using hv
  have output : v.regValue .rdi = stackPtr s - 1400 := by
    exact (effect.agrees.read (n := 64) (r := 7) (by simp)).trans
      (h.output.trans (ExponentTail.frame_address (off := 16) (by decide)))
  have ret : (returnBoundary v).rip = 0x1158ca := (callEffect_stack effect).1
  have binary : Field.BinaryFieldPre v boundary 0x1145e0 160 :=
    Field.BinaryFieldPre.of_stack ctx.toCalleePre callLayout (592-32*d)
      (by dsimp [callLayout]; omega) (by omega) (by dsimp [callLayout]; omega)
      frameV.bindingsSupported frameV.machine frameV.directionFlag frameV.loaded frameV.allocated
      effect.rip frameV.rsp left right output (by rw [ret]; exact inProgram_of_textOffset 0x158ca (by decide))
  have pre := exponent_montgomery_pre ctx frameV binary output (by decide) (by decide)
    ((effect.agrees.read (n := 64) (r := 1) (by simp)).trans h.modulus)
    ((effect.agrees.read (n := 64) (r := 8) (by simp)).trans h.negativeInverse)
  have callBytes {offset len i : Nat} (bound : offset+len ≤ 1416) (hi : i < len) :
      v.external[exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    rw [ExponentTail.frame_address (by omega)]
    exact scalar_call_byte (frameOffset := 1416) (by decide) h.frame.scalarFrame effect (by omega) (by omega) hi
  have vx : Field.MontgomeryAt v (v.regValue .rsi) y := by
    have addr : v.regValue .rsi = exponentFrameBase s + 0x30 := (effect.agrees.read (n := 64) (r := 6) (by simp)).trans h.left
    rw [addr]
    exact h.accumulator.of_bytes_eq (fun i hi => callBytes (by decide) hi)
  have vy : Field.MontgomeryAt v (v.regValue .rdx) (x^d % P256.Spec.Operations.domain.p) := by
    have addr : v.regValue .rdx = exponentFrameBase s + 0x338 + BitVec.ofNat 64 (32*d) := (effect.agrees.read (n := 64) (r := 2) (by simp)).trans h.right
    rw [addr]
    apply (h.constants.table d hd).of_bytes_eq
    intro i hi
    have hb := callBytes (offset := 0x338+32*d) (len := 32) (by omega) hi
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hb
  obtain ⟨w, result, product⟩ := dynamic_mul_correct pre vx vy
  have work := FieldCall.stack_result_work_frame ctx.toCalleePre frameV result output
    (by decide) (by decide) (by decide) (by decide)
  have scalarW := FieldCall.after_result ctx.toCalleePre frameV result (by decide) work
  have bytes {offset len i : Nat} (lo : 48 ≤ offset) (bound : offset+len ≤ 1368) (hi : i < len) :
      w.external[exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    have hc := callBytes (offset := offset) (by omega) hi
    rw [ExponentTail.frame_address (by omega)] at hc ⊢
    exact (FieldCall.stack_result_byte (frameOffset := 1416) (outputOffset := 1400) ctx.toCalleePre frameV result output
      (by decide) (by decide) (by omega) (by omega)
      (by change (1416-offset)+32 ≤ 1400 ∨ 1400+len ≤ 1416-offset; omega) hi).trans hc
  have frameW : ExponentFrame s w := ExponentFrame.of_scalarFrame scalarW
    ((exponent_word_of_bytes (n := 64) (fun i hi => bytes (offset := 0x2a0) (len := 8) (by decide) (by decide) hi)).trans h.frame.outputPointer)
  have constantsW := h.constants.of_upper_bytes ctx frameW (cutoff := 48) (by decide) (fun offset len lo bound i hi => bytes lo bound hi)
  have regs (r : Syntax.Reg) (hr : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      w.regValue r = t.regValue r := by
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  have savedWordW : exponentWordAt w (exponentFrameBase s + 0x2c0) (BitVec.ofNat 64 (n/16)) :=
    (exponent_word_of_bytes (n := 64) (fun i hi => bytes (offset := 0x2c0) (len := 8) (by decide) (by decide) hi)).trans h.savedWord
  have ripW : w.RIP = 0x1158ca := result.rip.trans ret
  have read : MemReadable w ((AddrMode.sib 4 none 0 (.d32 0x88)).addr w 0x1158d2) 8 := by
    change MemReadable w (w.regValue .rsp + 0x88) 8
    rw [frameW.rsp]
    exact frameW.stack_readable ctx (by decide)
  obtain ⟨u, step, readyU, load⟩ := (mov_r64_m64_effect_step 0x1158ca 0x4c
    (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 0x88))
      (by simp [AddrMode.Valid]) rfl rfl).advances
    (readyToStep frameW.machine frameW.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameW.loaded) 0x158ca
      [0x4c,0x8b,0x9c,0x24,0x88,0,0,0] (by decide) (by decide +kernel))
    ⟨ripW, read⟩ (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x158d2 (by decide)))
  change (movR64M64Effect 0x1158ca 11 (.sib 4 none 0 (.d32 0x88)) w).Holds w u at load
  have memory : u.external = w.external := load.agrees.external (by simp [Component.Covers])
  have byteMemory (a : BitVec 64) : u.external[a]? = w.external[a]? := congrArg (fun m : Ram => m[a]?) memory
  have position : ExponentPosition s u x n := by
    refine ⟨frameW.of_registers readyU load.agrees (by simp) (by simp [Component.Covers]),
      constantsW.of_memory byteMemory, ?_, exponentWordAt_of_memory byteMemory savedWordW,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (load.agrees.read (n := 64) (r := 5) (by simp)).trans ((regs .rbp (by simp)).trans h.word)
    · exact (load.agrees.read (n := 64) (r := 14) (by simp)).trans ((regs .r14 (by simp)).trans h.window)
    · exact (load.agrees.read (n := 64) (r := 3) (by simp)).trans ((regs .rbx (by simp)).trans h.firstWord)
    · exact (load.agrees.read (n := 64) (r := 13) (by simp)).trans ((regs .r13 (by simp)).trans h.firstWindow)
    · exact (load.agrees.read (n := 64) (r := 15) (by simp)).trans ((regs .r15 (by simp)).trans h.parameterPointer)
    · have hv : u.regValue .r11 = (Operand.mem (w.regValue .rsp + 0x88) : Operand 64).read w := load.writes
      rw [frameW.rsp] at hv
      exact hv.trans constantsW.modulus0
    · exact (load.agrees.read (n := 64) (r := 12) (by simp)).trans ((regs .r12 (by simp)).trans h.inverse)
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨u, 1+fuel+1, (run.trans execution).trans step, position, load.rip, ?_⟩
  have output' : v.regValue .rdi = exponentFrameBase s + 0x10 := (effect.agrees.read (n := 64) (r := 7) (by simp)).trans h.output
  rw [output'] at product
  exact montgomeryAt_of_memory byteMemory product

end P256.Proofs.Sec1.SquareRoot.ExponentMultiply
