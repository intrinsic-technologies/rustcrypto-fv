import P256.Proofs.Verifying.Combination.Output.Setup
import P256.Proofs.Program.ScalarFrame.Call

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem after_multi [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s entry 6560)
    (result : CalleeResult entry t boundary 96 1432)
    (output : entry.regValue .rdi = s.regValue .rdi) : State s t := by
  have bounds := stack_bounds pre.stack
  have sp : (stackPtr entry).toNat = (stackPtr s).toNat - 6560 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hw : MemoryWriteFrame entry t #v[registerRegion s .rdi 96, workRegion s 8808] := by
    intro a ha
    apply result.frame a
    intro region hr hin
    have hr' : region = registerRegion entry .rdi 96 ∨ region = Stack.region entry 1432 := by simpa using hr
    rcases hr' with rfl | rfl
    · apply ha (registerRegion s .rdi 96) (by simp)
      simpa only [registerRegion, output] using hin
    · apply ha (workRegion s 8808) (by simp)
      change (stackPtr s).toNat - 8808 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 8808 + 8760
      change (stackPtr entry).toNat - 1432 ≤ a.toNat ∧
        a.toNat < (Stack.region entry 1432).start + (Stack.region entry 1432).size at hin
      rw [stack_region_end, sp] at hin
      constructor <;> omega
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (output_work_frame pre hw), ?_, ?_, ?_,
    result.mxcsr.trans state.mxcsr, result.fp87.trans state.fp87⟩
  · have rsp : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [rsp, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · intro item hi
    have h : item.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (output_work_read pre (by decide) hw h (by omega)).trans (state.saved item hi)
  · have h := output_work_read pre (by decide) hw (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem transfer (correct : Loop.MultiCorrect) [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p q : Projective} {u v : Nat} (pre : Pre s boundary)
    (input : Preparation.Naf.MultiCallInput s t p q u v)
    (hu : u < 2^256) (hv : v < 2^256) (hp : p.valid) (hq : q.valid) :
    ∃ fuel w point, Advances boundary fuel t w ∧ State s w ∧ w.RIP = 0x1067a3 ∧
      ProjectiveAt w (s.regValue .rdi) point ∧ RepresentsSum point p q u v := by
  obtain ⟨entry, run, ready, effect⟩ := call_step (frameOffset := 6552) pre (by decide) (by decide)
    (readyToStep input.machine input.bindingsSupported) input.loaded input.allocated input.rsp
    0x679e 0x882d (by decide) (by decide +kernel) (by decide)
    (by change InProgram 0x10efd0; exact inProgram_of_textOffset 0xefd0 (by decide)) input.rip
  have frame := FrameState.after_call pre (by decide) (by decide) input.toFrameState ready effect
  have vin : entry.regValue .rsi = stackPtr s - 6240 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans input.input
  have vout : entry.regValue .rdi = s.regValue .rdi :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans input.output
  have ret : (returnBoundary entry).rip = 0x1067a3 := (callEffect_stack effect).1
  have cp := multi_pre pre frame effect.rip vin vout
    ((scalar_call_read (frameOffset := 6552) (by decide) input.toFrameState effect (offset := 6240) (n := 64) (by decide) (by decide)).trans input.tables)
    ((scalar_call_read (frameOffset := 6552) (by decide) input.toFrameState effect (offset := 6232) (n := 64) (by decide) (by decide)).trans input.tablesEnd)
    ((scalar_call_read (frameOffset := 6552) (by decide) input.toFrameState effect (offset := 6224) (n := 64) (by decide) (by decide)).trans input.digits)
    ((scalar_call_read (frameOffset := 6552) (by decide) input.toFrameState effect (offset := 6216) (n := 64) (by decide) (by decide)).trans input.digitsEnd)
    ((scalar_call_read (frameOffset := 6552) (by decide) input.toFrameState effect (offset := 6208) (n := 64) (by decide) (by decide)).trans input.beginIndex)
    ((scalar_call_read (frameOffset := 6552) (by decide) input.toFrameState effect (offset := 6200) (n := 64) (by decide) (by decide)).trans input.endIndex)
    (ret ▸ inProgram_of_textOffset 0x67a3 (by decide))
  have left := input.leftTable.of_copy (fun i hi => scalar_call_byte (frameOffset := 6552) (by decide)
    input.toFrameState effect (by decide) (by decide) hi)
  have right := input.rightTable.of_copy (fun i hi => scalar_call_byte (frameOffset := 6552) (by decide)
    input.toFrameState effect (by decide) (by decide) hi)
  have leftNaf := input.leftNaf.of_copy (fun i hi => scalar_call_byte (frameOffset := 6552) (by decide)
    input.toFrameState effect (by decide) (by decide) hi)
  have rightNaf := input.rightNaf.of_copy (fun i hi => scalar_call_byte (frameOffset := 6552) (by decide)
    input.toFrameState effect (by decide) (by decide) hi)
  have a768 : stackPtr s - 3120 + 768 = stackPtr s - 2352 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have a272 : stackPtr s - 4656 + 272 = stackPtr s - 4384 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  obtain ⟨w, point, result, value, sum⟩ := correct entry boundary (stackPtr s - 3120)
    (stackPtr s - 4656) p q u v cp left (a768 ▸ right) leftNaf (a272 ▸ rightNaf) hu hv hp hq
  obtain ⟨fuel, runW⟩ := result.execution
  exact ⟨1+fuel, w, point, run.trans runW, after_multi pre frame result vout,
    result.rip.trans ret, vout ▸ value, sum⟩

end P256.Proofs.Verifying.Combination.Output
