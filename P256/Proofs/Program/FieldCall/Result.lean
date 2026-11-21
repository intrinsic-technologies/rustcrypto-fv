import P256.Proofs.Field.Stack
import P256.Proofs.Program.ScalarFrame.Call
import X86Proofs.Instructions.Movs.RepTriple

set_option autoImplicit false

namespace P256.Proofs.Program.FieldCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open X86 X86.Machine X86.UserProcess X86Proofs

variable {outerEntry : BitVec 64} {outerInput outerOutput outerReserve frameOffset : Nat}

variable {inputRegister : Syntax.Reg}

theorem field_call_work_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister) (state : FrameState s t outerOutput outerReserve (BitVec.ofNat 64 frameOffset))
    (hframe : frameOffset + 8 ≤ outerReserve) (hsaved : 48 ≤ frameOffset)
    (effect : (callEffect target ret t).Holds t u) :
    MemoryWriteFrame t u #v[workRegion s outerReserve] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · refine ⟨workRegion s outerReserve, by simp, ?_⟩
    rw [scalar_call_address state] at ha
    exact work_contains pre hframe (by omega) ha
  · exact ha.elim

theorem stack_result_work_frame [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputOffset outputBytes reserve : Nat}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister) (state : FrameState s entry outerOutput outerReserve (BitVec.ofNat 64 (frameOffset + 8)))
    (result : CalleeResult entry t boundary outputBytes reserve)
    (destination : entry.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (hout : outputOffset ≤ outerReserve) (hsaved : outputBytes + 48 ≤ outputOffset)
    (hreserve : reserve + (frameOffset + 8) ≤ outerReserve) (hframe : 48 ≤ frameOffset) :
    MemoryWriteFrame entry t #v[workRegion s outerReserve] := by
  have hb := stack_bounds pre.stack
  have hsn : (stackPtr entry).toNat = (stackPtr s).toNat - (frameOffset + 8) := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (offset := frameOffset + 8) (by omega)
  have hdn : (entry.regValue .rdi).toNat = (stackPtr s).toNat - outputOffset := by
    rw [destination]
    exact stack_sub_toNat pre.stack hout
  intro a ha
  apply result.frame a
  intro r hr hin
  apply ha (workRegion s outerReserve) (by simp)
  have hr' : r = registerRegion entry .rdi outputBytes ∨ r = Stack.region entry reserve := by
    simpa using hr
  change (stackPtr s).toNat - outerReserve ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - outerReserve + (outerReserve - 48)
  rcases hr' with rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (entry.regValue .rdi).toNat + outputBytes at hin
    rw [hdn] at hin
    constructor <;> omega
  · change (stackPtr entry).toNat - reserve ≤ a.toNat ∧
      a.toNat < (Stack.region entry reserve).start + (Stack.region entry reserve).size at hin
    rw [stack_region_end] at hin
    change (stackPtr entry).toNat - reserve ≤ a.toNat ∧ a.toNat < (stackPtr entry).toNat + 8 at hin
    rw [hsn] at hin
    constructor <;> omega

theorem after_result [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    {outputBytes reserve : Nat}
    (pre : CalleePre s boundary outerEntry outerInput outerOutput outerReserve inputRegister) (state : FrameState s entry outerOutput outerReserve (BitVec.ofNat 64 (frameOffset + 8)))
    (result : CalleeResult entry t boundary outputBytes reserve)
    (hreserve : 48 ≤ outerReserve)
    (hf : MemoryWriteFrame entry t #v[workRegion s outerReserve]) : FrameState s t outerOutput outerReserve (BitVec.ofNat 64 frameOffset) := by
  have hw : MemoryWriteFrame entry t #v[registerRegion s .rdi outerOutput, workRegion s outerReserve] := by
    intro a ha
    apply hf a
    intro r hr
    exact ha r (by simpa using Or.inr hr)
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre hw), ?_, ?_, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have hsp : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [hsp, state.rsp]
    rw [BitVec.ofNat_add, ← BitVec.sub_sub]
    exact BitVec.sub_add_cancel _ _
  · intro entry he
    have hb : entry.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre hreserve hw hb (by omega)).trans (state.saved entry he)
  · have h := output_work_read pre hreserve hw (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress


end P256.Proofs.Program.FieldCall
