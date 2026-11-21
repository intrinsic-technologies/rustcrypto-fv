import P256.Proofs.Ecdh.Interface
import P256.Proofs.Projective.Multiply.Machine.Loop.Correct
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.FieldCall.Memory
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Ecdh

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall
open Projective.Multiply

private theorem table_address (s : RamState) : frameBase s + 248 = stackPtr s - 1808 := by
  simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

private theorem output_address (s : RamState) : frameBase s + 152 = stackPtr s - 1904 := by
  simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

private theorem digits_address (s : RamState) : frameBase s + 80 = stackPtr s - 1976 := by
  simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

theorem multiply_correct [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {d : Nat} {point : Standards.SECG.ECC.Curve.Point}
    (pre : Pre s boundary) (state : Ready s t d point) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Multiplied s u (model (ProjectiveWrapper.Decode.projective point) d) := by
  obtain ⟨v,run,ready,effect⟩ := scalar_call pre.toCalleePre (by decide) (by decide) state.toFrameState
    0x33b 0x2f10 (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x3250 (by decide)) state.rip
  have frame : FrameState s v 32 3464 2064 :=
    state.toFrameState.after_call pre.toCalleePre (by decide) (by decide) ready effect
  have srcV : v.regValue .rsi = stackPtr s - 1808 :=
    ((effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.source).trans (table_address s)
  have dstV : v.regValue .rdi = stackPtr s - 1904 :=
    ((effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.destination).trans (output_address s)
  have digV : v.regValue .rcx = stackPtr s - 1976 :=
    ((effect.agrees.read (n := 64) (r := 1) (by simp)).trans state.digits).trans (digits_address s)
  have ret : (returnBoundary v).rip = 0x100340 := (callEffect_stack effect).1
  have retIn : InProgram (returnBoundary v).rip :=
    ret ▸ inProgram_of_textOffset 0x340 (by decide)
  have cp : CalleePre v boundary 0x103250 768 96 1400 :=
    CalleePre.of_stack pre.toCalleePre
      (⟨2064,1808,1904,by decide,by decide,by decide,by decide,by decide,by decide,
        .inr (by decide)⟩ : StackCallLayout 3464 768 96 1400)
      frame.bindingsSupported frame.machine frame.directionFlag frame.loaded frame.allocated
      effect.rip frame.rsp srcV dstV retIn
  have dp : CalleePre v boundary 0x103250 65 96 1400 .rcx :=
    CalleePre.of_stack pre.toCalleePre
      (⟨2064,1976,1904,by decide,by decide,by decide,by decide,by decide,by decide,
        .inl (by decide)⟩ : StackCallLayout 3464 65 96 1400)
      frame.bindingsSupported frame.machine frame.directionFlag frame.loaded frame.allocated
      effect.rip frame.rsp digV dstV retIn
  have loopPre : Projective.Multiply.Machine.Loop.Pre v boundary :=
    { cp with
      tableCount := (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.tableCount
      digitCount := (effect.agrees.read (n := 64) (r := 8) (by simp)).trans state.digitCount
      digitsBounded := dp.inputBounded
      digitsAllocated := dp.inputAllocated
      digitsOutput := dp.separation 0 1 (by decide)
      digitsStack := dp.separation 0 2 (by decide) }
  have tableV : Projective.Multiply.Machine.Lookup.TableAt v (v.regValue .rsi)
      (Projective.table (ProjectiveWrapper.Decode.projective point)) := by
    rw [srcV, ← table_address]
    intro index
    apply (state.table index).of_bytes_eq
    intro i hi
    rw [table_address, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact scalar_call_byte (offset := 1808) (len := 768) (by decide) state.toFrameState effect
      (by decide) (by decide) (by have := index.isLt; omega)
  have digitsV : Bytes v.external (v.regValue .rcx) 65
      (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i)) := by
    rw [digV]
    intro i hi
    apply (scalar_call_byte (offset := 1976) (len := 65) (by decide) state.toFrameState effect
      (by decide) (by decide) hi).trans
    change t.external[stackPtr s - 1976 + BitVec.ofNat 64 i]? = _
    rw [← digits_address]
    exact state.digitBytes i hi
  obtain ⟨u,result,value⟩ := Projective.Multiply.Machine.Loop.loop_correct loopPre tableV
  rw [Projective.Multiply.Machine.Loop.linearCombination_eq_model digitsV] at value
  obtain ⟨fuel,executed⟩ := result.execution
  refine ⟨1+fuel,u,run.trans executed,
    after_result pre.toCalleePre (frameOffset := 2056) frame result (by decide)
      (stack_result_work_frame pre.toCalleePre (frameOffset := 2056) frame result dstV
        (by decide) (by decide) (by decide) (by decide)), result.rip.trans ret, ?_, ?_⟩
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effect.agrees.read (n := 64) (r := 3) (by simp)).trans state.output)
  · rw [dstV, ← output_address] at value
    exact value

end P256.Proofs.Ecdh
