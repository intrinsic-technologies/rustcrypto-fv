import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prologue
import P256.Proofs.Sec1.SquareRoot.Exponent.CallPre
import P256.Proofs.Sec1.SquareRoot.Exponent.Finish.Memory
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem table_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y i : Nat}
    (ctx : ExponentPre s boundary x) (frame : Frame s t) (hi : i<15)
    (offset : Nat) (disp : BitVec 32) (bound : offset+5<118431)
    (code : Extracted.textBytes.toListFrom offset 5=encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress+BitVec.ofNat 64 offset) 5 (disp.signExtend 64)=0x1145e0)
    (rip : t.RIP=Extracted.textAddress+BitVec.ofNat 64 offset)
    (left : t.regValue .rsi=exponentFrameBase s+BitVec.ofNat 64 (0xa0+32*i))
    (right : t.regValue .rdx=exponentFrameBase s+0x2f8)
    (destination : t.regValue .rdi=exponentFrameBase s+0x10)
    (modulus : t.regValue .rcx=s.regValue .rsi+32) (inverse : t.regValue .r8=1)
    (vx : Field.MontgomeryAt t (exponentFrameBase s+BitVec.ofNat 64 (0xa0+32*i)) y)
    (vy : Field.MontgomeryAt t (exponentFrameBase s+0x2f8) x) :
    ∃ u fuel, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP=Extracted.textAddress+BitVec.ofNat 64 (offset+5) ∧
      Field.MontgomeryAt u (exponentFrameBase s+0x10) (y*x%P256.Spec.Operations.domain.p) ∧
      CalleeSavedRegistersUnchanged t u ∧
      (∀ off len : Nat, 48≤off → off+len≤1368 → ∀ j<len,
        u.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 j]?=
          t.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 j]?) := by
  have ht : InProgram (branchTarget (Extracted.textAddress+BitVec.ofNat 64 offset) 5
      (disp.signExtend 64)) := by rw [target]; exact inProgram_of_textOffset 0x145e0 (by decide)
  obtain ⟨v,run,ready,effect⟩ := ScalarFrame.scalar_call ctx.toCalleePre (by decide) (by decide)
    frame offset disp (by omega) code (by rw [target]; decide) ht rip
  have frameV := frame.after_call ctx.toCalleePre (by decide) (by decide) ready effect
  have lv : v.regValue .rsi=stackPtr s-BitVec.ofNat 64 (1416-(0xa0+32*i)) :=
    ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans left).trans
      (ExponentTail.frame_address (by omega))
  have rv : v.regValue .rdx=stackPtr s-656#64 :=
    ((effect.agrees.read (n := 64) (r := 2) (by simp)).trans right).trans
      (ExponentTail.frame_address (off := 760) (by decide))
  have dv : v.regValue .rdi=stackPtr s-1400#64 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination).trans
      (ExponentTail.frame_address (off := 16) (by decide))
  have ret : (returnBoundary v).rip=Extracted.textAddress+BitVec.ofNat 64 (offset+5) := by
    have h : (returnBoundary v).rip=Extracted.textAddress+BitVec.ofNat 64 offset+5 := (callEffect_stack effect).1
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using h
  let layout : StackCallLayout 1584 32 32 160 :=
    ⟨1424,1416-(0xa0+32*i),1400,by decide,by decide,by omega,by decide,
      by omega,by decide,by omega⟩
  have binary : Field.BinaryFieldPre v boundary 0x1145e0 160 :=
    Field.BinaryFieldPre.of_stack ctx.toCalleePre layout 656
      (by change 656+8≤1424; decide) (by decide) (by change 1400+32≤656 ∨ 656+32≤1400; decide) frameV.bindingsSupported frameV.machine
      frameV.directionFlag frameV.loaded frameV.allocated (effect.rip.trans target)
      frameV.rsp lv rv dv (by rw [ret]; exact inProgram_of_textOffset _ bound)
  have pre := exponent_montgomery_pre ctx frameV binary dv (by decide) (by decide)
    ((effect.agrees.read (n := 64) (r := 1) (by simp)).trans modulus)
    ((effect.agrees.read (n := 64) (r := 8) (by simp)).trans inverse)
  have callBytes {off len j : Nat} (hbound : off+len≤1416) (hj : j<len) :
      v.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 j]?=
        t.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 j]? := by
    rw [ExponentTail.frame_address (by omega)]
    exact ScalarFrame.scalar_call_byte (frameOffset := 1416) (by decide) frame effect
      (by omega) (by omega) hj
  have leftV : v.regValue .rsi=exponentFrameBase s+BitVec.ofNat 64 (0xa0+32*i) :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans left
  have rightV : v.regValue .rdx=exponentFrameBase s+0x2f8 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans right
  have destV : v.regValue .rdi=exponentFrameBase s+0x10 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have vleft : Field.MontgomeryAt v (v.regValue .rsi) y := by
    rw [leftV]
    exact vx.of_bytes_eq (fun j hj ↦ callBytes (by omega) hj)
  have vright : Field.MontgomeryAt v (v.regValue .rdx) x := by
    rw [rightV]
    exact vy.of_bytes_eq (fun j hj ↦ callBytes (by decide) hj)
  obtain ⟨u,result,product⟩ := dynamic_mul_correct pre vleft vright
  have work := FieldCall.stack_result_work_frame ctx.toCalleePre frameV result dv
    (by decide) (by decide) (by decide) (by decide)
  have final := FieldCall.after_result ctx.toCalleePre frameV result (by decide) work
  obtain ⟨fuel,execution⟩ := result.execution
  refine ⟨u,1+fuel,run.trans execution,final,result.rip.trans ret,?_,?_,?_⟩
  · rwa [destV] at product
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  · intro off len lo hb j hj
    have hc := callBytes (off := off) (by omega) hj
    rw [ExponentTail.frame_address (by omega)] at hc ⊢
    exact (FieldCall.stack_result_byte (frameOffset := 1416) (outputOffset := 1400)
      ctx.toCalleePre frameV result dv (by decide) (by decide) (by omega) (by omega)
      (by change (1416-off)+32≤1400 ∨ 1400+len≤1416-off; omega) hj).trans hc

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
