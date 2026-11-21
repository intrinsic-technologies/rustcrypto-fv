import P256.Proofs.Sec1.Decode.Prepare.State
import P256.Proofs.Program.ScalarFrame.Input
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}

theorem stack_readable (pre : DecodePre s boundary bytes) (state : Frame s t)
    {offset len : Nat} (bound : offset + len ≤ 312) :
    MemReadable t (stackPtr t + BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 312) state.rsp (by decide) (by omega)]
  exact readable_of_grow
    (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated

theorem stack_writable (pre : DecodePre s boundary bytes) (state : Frame s t)
    {offset len : Nat} (bound : offset + len ≤ 312) (positive : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      (stackPtr t + BitVec.ofNat 64 offset) len := by
  have readable := stack_readable pre state bound
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved positive readable.low
  intro i hi reserved
  apply pre.avoids (Stack.region s 3680) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ?_ (.inr reserved)
  rw [ScalarFrame.scalar_stack_address (frameOffset := 312) state.rsp (by decide) (by omega)]
  exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ⟨i, hi, rfl⟩

theorem stack_code (pre : DecodePre s boundary bytes) (state : Frame s t)
    {offset len codeOffset codeLen : Nat} (bound : offset + len ≤ 312)
    (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 3680) (by simp)
    (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  · rw [ScalarFrame.scalar_stack_address (frameOffset := 312) state.rsp (by decide) (by omega)]
    exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ⟨i, hi, rfl⟩
  · apply Or.inl
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset + j) (by omega)

theorem stack_work (pre : DecodePre s boundary bytes) (state : Frame s t)
    {offset len : Nat} {a : BitVec 64} (bound : offset + len ≤ 280)
    (covered : (Component.mem (stackPtr t + BitVec.ofNat 64 offset) len).Covers a) :
    (ScalarFrame.Work.region s 3680 32).Contains a.toNat := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 312) state.rsp (by decide) (by omega)] at covered
  exact ScalarFrame.Work.contains pre.toCalleePre (by omega) (by omega) covered

theorem input_bytes (pre : DecodePre s boundary bytes) (state : Frame s t) :
    (registerRegion s .rsi bytes.size).HasBytes t.external bytes :=
  ScalarFrame.input_bytes_of_frame pre.toCalleePre state.frame pre.input

theorem after_callee {v u : RamState} {target returnRip : BitVec 64}
    {outputBytes reserve : Nat} (pre : DecodePre s boundary bytes) (state : Frame s t)
    (effect : (callEffect (fun _ ↦ target) returnRip t).Holds t v)
    (result : CalleeResult v u boundary outputBytes reserve)
    (memory : MemoryWriteFrame t u
      #v[registerRegion s .rdi 80, ScalarFrame.Work.region s 3680 32]) :
    Frame s u := by
  have total := memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre.toCalleePre memory)
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    fun a ha ↦ result.allocated a (effect.agrees.grow a (state.allocated a ha)), total,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change stackPtr u = stackPtr s - 312
    have rsp : stackPtr u = stackPtr v + 8 := result.rsp
    rw [rsp, (callEffect_stack effect).2, state.rsp]
  · intro slot member
    have bound : slot.2 ≤ 32 := by
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact (ScalarFrame.Work.read pre.toCalleePre (by decide) memory bound (by omega)).trans
      (state.saved slot member)
  · have h := ScalarFrame.Work.read pre.toCalleePre (by decide) memory
      (offset := 0) (n := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (result.calleeSaved .rbp (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 5) (by simp)).trans (state.registers .rbp (by simp)))
    · exact (result.calleeSaved .r13 (by simp)).trans
        ((effect.agrees.read (n := 64) (r := 13) (by simp)).trans (state.registers .r13 (by simp)))
  · exact result.mxcsr.trans ((effect.agrees.mxcsr (by simp)).trans state.mxcsr)
  · exact result.fp87.trans ((effect.agrees.fcw (by simp)).trans state.fp87)

end P256.Proofs.Sec1.Decode.Prepare
