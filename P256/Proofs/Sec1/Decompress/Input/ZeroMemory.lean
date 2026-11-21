import P256.Proofs.Sec1.Decompress.Input.Zero
import P256.Proofs.Sec1.Decompress.Input.FinalZero
import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Sec1.Decompress.Cubic.Support
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field

theorem zero_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x10fcfc) : ZeroPre t := by
  refine ⟨rip, ?_, ?_⟩
  · intro i n hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have addr : stackPtr t + 32 = stackPtr s - 376 :=
        Cubic.input_stack_address state.rsp (offset := 32) (by decide)
      change MemWritable t (stackPtr t + 32) 1
      rw [addr]
      exact writable_of_grow (stack_sub_writable pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide) (by decide) (by omega)) state.allocated
    · have addr : stackPtr t + 104 = stackPtr s - 304 :=
        Cubic.input_stack_address state.rsp (offset := 104) (by decide)
      change MemWritable t (stackPtr t + 104) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 96 = stackPtr s - 312 :=
        Cubic.input_stack_address state.rsp (offset := 96) (by decide)
      change MemWritable t (stackPtr t + 96) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 88 = stackPtr s - 320 :=
        Cubic.input_stack_address state.rsp (offset := 88) (by decide)
      change MemWritable t (stackPtr t + 88) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 80 = stackPtr s - 328 :=
        Cubic.input_stack_address state.rsp (offset := 80) (by decide)
      change MemWritable t (stackPtr t + 80) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
  · intro i n hi offset len hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals change RangeApart (stackPtr t + _) _ _ _
    all_goals exact ScalarFrame.stack_code pre state (by decide) (by decide) hc

theorem zero_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (ready : ReadyToStep u) (effect : (zeroEffect t).Holds t u) : Frame s u := by
  apply state.after_effect pre (by decide) ready effect.agrees
  · intro c hc address hv
    simp only [zeroEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals obtain ⟨i, hi, rfl⟩ := hv
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 376) (len := 1) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 32) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 328) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 80) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 320) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 88) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 312) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 96) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 304) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 104) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
  · simp [zeroEffect, Effect.components]

theorem zero_byte {t u : RamState} (effect : (zeroEffect t).Holds t u)
    {off len : Nat} (bound : off+len < 2^64)
    (tagApart : off+len ≤ 32 ∨ 33 ≤ off)
    (zeroApart : off+len ≤ 80 ∨ 112 ≤ off)
    {i : Nat} (hi : i < len) :
    u.external[stackPtr t + BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc hv
  simp only [zeroEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  all_goals obtain ⟨j, hj, he⟩ := hv
  · exact RangeApart.offsets (stackPtr t) (a := 32) (b := off)
      (by decide) (by omega) (by rcases tagApart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 80) (b := off)
      (by decide) (by omega) (by rcases zeroApart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 88) (b := off)
      (by decide) (by omega) (by rcases zeroApart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 96) (b := off)
      (by decide) (by omega) (by rcases zeroApart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 104) (b := off)
      (by decide) (by omega) (by rcases zeroApart with h | h <;> omega) j hj i hi he.symm

theorem zero_read {t u : RamState} (effect : (zeroEffect t).Holds t u)
    {off n : Nat} (bound : off+n/8 < 2^64)
    (tagApart : off+n/8 ≤ 32 ∨ 33 ≤ off)
    (zeroApart : off+n/8 ≤ 80 ∨ 112 ≤ off) :
    (Operand.mem (stackPtr t+BitVec.ofNat 64 off) : Operand n).read u =
      (Operand.mem (stackPtr t+BitVec.ofNat 64 off) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  exact zero_byte effect bound tagApart zeroApart hi

theorem zero_value [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (effect : (zeroEffect t).Holds t u) : MontgomeryAt u (stackPtr t+80) 0 := by
  apply Field.montgomeryAt_of_memLoad_limbs (by decide +kernel)
  · intro i hi
    have addr : stackPtr t + 80 = stackPtr s - 328 := Cubic.input_stack_address state.rsp (offset := 80) (by decide)
    rw [addr]
    exact effect.agrees.grow _ (state.allocated _ ((stack_sub_readable pre.stack (by decide) (by decide)).mem i hi))
  · intro j hj
    simp only [Nat.zero_mul, Nat.zero_mod, Nat.zero_div]
    have hw := effect.writes
    have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.2.2
theorem finalZero_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x10fd75) : FinalZeroPre t := by
  refine ⟨rip, ?_, ?_⟩
  · intro i n hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have addr : stackPtr t + 288 = stackPtr s - 120 :=
        Cubic.input_stack_address state.rsp (offset := 288) (by decide)
      change MemWritable t (stackPtr t + 288) 1
      rw [addr]
      exact writable_of_grow (stack_sub_writable pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide) (by decide) (by omega)) state.allocated
    · have addr : stackPtr t + 248 = stackPtr s - 160 :=
        Cubic.input_stack_address state.rsp (offset := 248) (by decide)
      change MemWritable t (stackPtr t + 248) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 240 = stackPtr s - 168 :=
        Cubic.input_stack_address state.rsp (offset := 240) (by decide)
      change MemWritable t (stackPtr t + 240) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 232 = stackPtr s - 176 :=
        Cubic.input_stack_address state.rsp (offset := 232) (by decide)
      change MemWritable t (stackPtr t + 232) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · have addr : stackPtr t + 224 = stackPtr s - 184 :=
        Cubic.input_stack_address state.rsp (offset := 224) (by decide)
      change MemWritable t (stackPtr t + 224) 8
      rw [addr]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
  · intro i n hi offset len hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals change RangeApart (stackPtr t + _) _ _ _
    all_goals exact ScalarFrame.stack_code pre state (by decide) (by decide) hc

theorem finalZero_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (ready : ReadyToStep u) (effect : (finalZeroEffect t).Holds t u) : Frame s u := by
  apply state.after_effect pre (by decide) ready effect.agrees
  · intro c hc address hv
    simp only [finalZeroEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    all_goals obtain ⟨i, hi, rfl⟩ := hv
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 120) (len := 1) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 288) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 184) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 224) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 176) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 232) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 168) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 240) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
    · exact ⟨ScalarFrame.workRegion s 2592, by simp,
        ScalarFrame.work_contains pre (offset := 160) (len := 8) (by decide) (by decide)
          (by rw [← Cubic.input_stack_address state.rsp (offset := 248) (by decide)]; exact ⟨i, hi, rfl⟩)⟩
  · simp [finalZeroEffect, Effect.components]

theorem finalZero_byte {t u : RamState} (effect : (finalZeroEffect t).Holds t u)
    {off len : Nat} (bound : off+len < 2^64)
    (tagApart : off+len ≤ 288 ∨ 289 ≤ off)
    (zeroApart : off+len ≤ 224 ∨ 256 ≤ off)
    {i : Nat} (hi : i < len) :
    u.external[stackPtr t + BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
  apply effect.agrees.byte
  intro c hc hv
  simp only [finalZeroEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  all_goals obtain ⟨j, hj, he⟩ := hv
  · exact RangeApart.offsets (stackPtr t) (a := 288) (b := off)
      (by decide) (by omega) (by rcases tagApart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 224) (b := off)
      (by decide) (by omega) (by rcases zeroApart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 232) (b := off)
      (by decide) (by omega) (by rcases zeroApart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 240) (b := off)
      (by decide) (by omega) (by rcases zeroApart with h | h <;> omega) j hj i hi he.symm
  · exact RangeApart.offsets (stackPtr t) (a := 248) (b := off)
      (by decide) (by omega) (by rcases zeroApart with h | h <;> omega) j hj i hi he.symm

theorem finalZero_read {t u : RamState} (effect : (finalZeroEffect t).Holds t u)
    {off n : Nat} (bound : off+n/8 < 2^64)
    (tagApart : off+n/8 ≤ 288 ∨ 289 ≤ off)
    (zeroApart : off+n/8 ≤ 224 ∨ 256 ≤ off) :
    (Operand.mem (stackPtr t+BitVec.ofNat 64 off) : Operand n).read u =
      (Operand.mem (stackPtr t+BitVec.ofNat 64 off) : Operand n).read t := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  exact finalZero_byte effect bound tagApart zeroApart hi

theorem finalZero_value [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (effect : (finalZeroEffect t).Holds t u) : MontgomeryAt u (stackPtr t+224) 0 := by
  apply Field.montgomeryAt_of_memLoad_limbs (by decide +kernel)
  · intro i hi
    have addr : stackPtr t + 224 = stackPtr s - 184 := Cubic.input_stack_address state.rsp (offset := 224) (by decide)
    rw [addr]
    exact effect.agrees.grow _ (state.allocated _ ((stack_sub_readable pre.stack (by decide) (by decide)).mem i hi))
  · intro j hj
    simp only [Nat.zero_mul, Nat.zero_mod, Nat.zero_div]
    have hw := effect.writes
    have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.2.1
    · simpa (config := {decide := true}) only [x86_compose, Write.AllHold, stackPtr, BitVec.add_assoc, Operand.read_reg64] using hw.2.2.2.2

end P256.Proofs.Sec1.Decompress.Input
