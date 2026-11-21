import P256.Proofs.Nonce.Fill.Work
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s called t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original : State}

theorem Frame.after_call_result (pre : Pre initial boundary orderAddress original)
    (frame : Frame initial s) {target : RamState → BitVec 64} {ret : BitVec 64}
    {outputBytes reserve : Nat} {outputRegister : Syntax.Reg}
    (effect : (callEffect target ret s).Holds s called)
    (result : CalleeResult called t boundary outputBytes reserve outputRegister)
    (memory : MemoryWriteFrame s t (workRegions initial)) : Frame initial t := by
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha => result.allocated a (effect.agrees.grow a (frame.allocated a ha)),
    memoryWriteFrame_trans frame.frame (work_frame pre memory),
    result.rsp.trans ((callEffect_stack effect).2.trans frame.rsp), ?_, ?_,
    result.mxcsr.trans ((effect.agrees.mxcsr (by simp)).trans frame.mxcsr),
    result.fp87.trans ((effect.agrees.fcw (by simp)).trans frame.fp87)⟩
  · intro item member
    have bound : item.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (work_read pre memory bound (by omega)).trans (frame.saved item member)
  · have h := work_read pre memory (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans frame.returnAddress

omit [Bindings] in
theorem Slots.of_stack_reads (slots : Slots initial s)
    (read : ∀ offset n : Nat, offset ≤ 232 → n / 8 ≤ offset + 8 →
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) n =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) n) :
    Slots initial t := by
  have shifted {offset n : Nat} (bound : offset ≤ 232) (span : n / 8 ≤ 232 - offset + 8) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 offset) n =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) n := by
    rw [frameBase_add initial bound]
    exact read _ _ (by omega) span
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (shifted (offset := 40) (by decide) (by decide)).trans slots.outputSlot
  · exact (shifted (offset := 48) (by decide) (by decide)).trans slots.lengthSlot
  · exact (shifted (offset := 56) (by decide) (by decide)).trans slots.bitsSlot
  · exact (shifted (offset := 64) (by decide) (by decide)).trans slots.statePointerSlot
  · exact (shifted (offset := 136) (by decide) (by decide)).trans slots.valuePointerSlot
  · exact (shifted (offset := 144) (by decide) (by decide)).trans slots.generatorPointerSlot

end P256.Proofs.Nonce.Fill
