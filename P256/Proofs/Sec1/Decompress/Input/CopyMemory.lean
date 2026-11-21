import P256.Proofs.Sec1.Decompress.Input.Copy
import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Sec1.Decompress.Cubic.Support
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field

theorem copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x10fd41) : CopyPre t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_readable pre state (by decide) (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · have addr : stackPtr t + 256 = stackPtr s - 152 :=
        Cubic.input_stack_address state.rsp (offset := 256) (by decide)
      change MemWritable t (stackPtr t + 256) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 264 = stackPtr s - 144 :=
        Cubic.input_stack_address state.rsp (offset := 264) (by decide)
      change MemWritable t (stackPtr t + 264) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 272 = stackPtr s - 136 :=
        Cubic.input_stack_address state.rsp (offset := 272) (by decide)
      change MemWritable t (stackPtr t + 272) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 280 = stackPtr s - 128 :=
        Cubic.input_stack_address state.rsp (offset := 280) (by decide)
      change MemWritable t (stackPtr t + 280) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
  · intro i hi offset len hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_code pre state (by decide) (by decide) hc

theorem copy_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (ready : ReadyToStep u) (effect : (copyEffect t).Holds t u) : Frame s u := by
  apply state.after_effect pre (by decide) ready effect.agrees
  · intro c hc address hv
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, Write.component_reg, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals obtain ⟨i,hi,rfl⟩ := hv
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 152) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 256) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 144) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 264) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 136) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 272) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 128) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 280) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
  · simp [copyEffect, Effect.components]

theorem copy_read {t u : RamState} (effect : (copyEffect t).Holds t u)
    {off n : Nat} (bound : off+n/8 < 2^64)
    (apart : off+n/8 ≤ 256 ∨ 288 ≤ off) :
    (Operand.mem (stackPtr t+BitVec.ofNat 64 off) : Operand n).read u =
      (Operand.mem (stackPtr t+BitVec.ofNat 64 off) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply effect.agrees.byte
  intro c hc hv
  simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, Write.component_reg, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  all_goals obtain ⟨j,hj,he⟩ := hv
  · exact RangeApart.offsets (stackPtr t) (a := 256) (b := off)
      (by decide) (by omega) (by rcases apart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 264) (b := off)
      (by decide) (by omega) (by rcases apart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 272) (b := off)
      (by decide) (by omega) (by rcases apart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 280) (b := off)
      (by decide) (by omega) (by rcases apart with h | h <;> omega) j hj i hi he.symm

theorem copy_value [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (effect : (copyEffect t).Holds t u) (input : MontgomeryAt t (stackPtr t+80) x) :
    MontgomeryAt u (stackPtr t+256) x := by
  apply Field.montgomeryAt_of_memLoad_limbs input.1
  · intro i hi
    have addr : stackPtr t + 256 = stackPtr s - 152 := Cubic.input_stack_address state.rsp (offset := 256) (by decide)
    rw [addr]
    exact effect.agrees.grow _ (state.allocated _ ((stack_sub_readable pre.stack (by decide) (by decide)).mem i hi))
  · intro j hj
    rw [← input.memLoad_limb j hj]
    have hw := effect.writes
    have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.2.2.2

end P256.Proofs.Sec1.Decompress.Input
