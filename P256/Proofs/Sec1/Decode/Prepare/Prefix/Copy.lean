import P256.Proofs.Sec1.Decode.Prepare.Prefix.Fill
import P256.Proofs.Program.Copy
import P256.Proofs.Program.ScalarFrame.CallStep

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}

theorem copy (pre : DecodePre s boundary bytes) (state : Frame s t)
    (shape : EncodingShape bytes) (rip : t.RIP = 0x10e55b)
    (destination : t.regValue .rdi = stackPtr s - 312#64)
    (source : t.regValue .rsi = s.regValue .rsi)
    (count : t.regValue .rdx = BitVec.ofNat 64 bytes.size)
    (output : t.regValue .r15 = s.regValue .rdi) (zero : t.regValue .r12 = 0)
    (padding : ∀ i < 65, bytes.size ≤ i → t.external[stackPtr s - 312#64 + BitVec.ofNat 64 i]? = some 0) :
    ∃ n u, Advances boundary n t u ∧ BufferReady s u bytes := by
  have bound : bytes.size ≤ 65 := by have := shape.size; omega
  obtain ⟨v, runV, ready, effect⟩ := memory_call true pre state rip
  have sp : stackPtr v = stackPtr s - 320#64 := effect.writes.1.trans (push_address state)
  have dst : v.regValue .rdi = stackPtr s - 312#64 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have src : v.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  let layout : StackBufferLayout 3680 bytes.size 0 := ⟨320,312,by decide,by decide,by decide,by omega⟩
  have child : CalleePre v boundary 0x11c930 bytes.size bytes.size 0 :=
    pre.toCalleePre.of_input_and_stack layout
      (bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees)
      (supportedMachine_of_ready_agrees state.machine ready effect.agrees)
      (effect.agrees.directionFlagClear (by simp) state.directionFlag)
      (push_loaded pre state effect) (fun a ha ↦ effect.agrees.grow a (state.allocated a ha))
      effect.rip sp src dst (by
        change InProgram (stackTop v)
        rw [(callEffect_stack effect).1]
        exact inProgram_of_textOffset 0xe561 (by decide))
  obtain ⟨u, result, copied, _⟩ := memcpy_correct child
    ((effect.agrees.read (n := 64) (r := 2) (by simp)).trans count) (by omega)
  obtain ⟨n, runU⟩ := result.execution
  refine ⟨1+n,u,runV.trans runU,⟨after_callee pre state effect result
    (result_memory (offset := 312) pre state effect dst (by decide) (by omega) result),
    result.rip.trans (callEffect_stack effect).1,
    (memory_callee_saved effect result .r15 (by simp)).trans output,
    (memory_callee_saved effect result .r12 (by simp)).trans zero, shape, ?_⟩⟩
  intro i hi
  change u.external[stackPtr s - 312#64 + BitVec.ofNat 64 i]? = _
  by_cases inside : i < bytes.size
  · have input := ScalarFrame.input_bytes_of_frame pre.toCalleePre
      (memoryWriteFrame_trans state.frame (ScalarFrame.Work.frame pre.toCalleePre
        (effect.agrees.memoryWriteFrame (push_writes pre state)))) pre.input
    have hb := input.2 ⟨i,inside⟩
    simp only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    have h := copied i inside
    rw [dst,src] at h
    rw [h, hb]
    simp only [Array.getElem?_eq_getElem (show i < bytes.data.size from inside),
      Option.getD_some, ByteArray.getElem_eq_getElem_data]
  · have bounds := stack_bounds pre.stack
    have addr : (stackPtr s - 312#64 + BitVec.ofNat 64 i).toNat = (stackPtr s).toNat - 312 + i := by
      rw [toNat_add_ofNat _ _ (by rw [stack_sub_toNat pre.stack (by decide : 312 ≤ 3680)]; omega),
        stack_sub_toNat pre.stack (by decide : 312 ≤ 3680)]
    have mem : u.external[stackPtr s - 312#64 + BitVec.ofNat 64 i]? =
        v.external[stackPtr s - 312#64 + BitVec.ofNat 64 i]? := by
      apply result.frame
      intro region hr hin
      have cases : region = registerRegion v .rdi bytes.size ∨ region = Stack.region v 0 := by simpa using hr
      rcases cases with rfl | rfl
      · change (v.regValue .rdi).toNat ≤ _ ∧ _ < (v.regValue .rdi).toNat + bytes.size at hin
        rw [dst, addr, stack_sub_toNat pre.stack (by decide : 312 ≤ 3680)] at hin
        omega
      · change (stackPtr v).toNat - 0 ≤ _ ∧ _ < (Stack.region v 0).start + (Stack.region v 0).size at hin
        rw [stack_region_end,sp,addr,stack_sub_toNat pre.stack (by decide : 320 ≤ 3680)] at hin
        omega
    have old := ScalarFrame.call_byte (frameOffset := 312) (by decide) state.rsp effect
      (offset := 312) (len := 65) (by decide) (by decide) hi
    rw [mem,old,padding i hi (by omega)]
    rw [Array.getElem?_eq_none (show bytes.data.size ≤ i from Nat.le_of_not_gt inside)]
    rfl

end P256.Proofs.Sec1.Decode.Prepare
