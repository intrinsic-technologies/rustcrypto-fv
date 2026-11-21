import P256.Proofs.Projective.Double.Output.Copy

set_option autoImplicit false


namespace P256.Proofs.Projective.Double.Output

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_covers {t : RamState} {next : BitVec 64} {src : BitVec 5}
    {source target : Nat} {c : Component} {a : BitVec 64}
    (hc : c ∈ (copyEffect next src source target t).components) (ha : c.Covers a) :
    (Component.mem (stackPtr t + BitVec.ofNat 64 target) 32).Covers a := by
  simp only [copyEffect, Copy32.effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.append_nil, List.cons_append, List.nil_append] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha.elim
  · exact ha.elim
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨i, by omega, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨8+i, by omega, ?_⟩
    simp only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨16+i, by omega, ?_⟩
    simp only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨24+i, by omega, ?_⟩
    simp only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · exact ha.elim

theorem copy_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {next : BitVec 64} {src : BitVec 5} {source target : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (ready : ReadyToStep u) (effect : (copyEffect next src source target t).Holds t u)
    (bound : target + 80 ≤ 728) : FrameState s u 96 1016 728 := by
  apply FrameState.after_effect pre (by decide) state ready effect.agrees ?_ ?_
  · intro c hc a ha
    have covers := copy_covers hc ha
    rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) (by omega)] at covers
    exact ⟨workRegion s 1016, by simp, work_contains pre (by omega) (by omega) covers⟩
  · simp [copyEffect, Copy32.effect, Effect.components]

theorem copy_stack_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {next : BitVec 64} {src : BitVec 5} {source target : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (effect : (copyEffect next src source target t).Holds t u)
    (bound : target + 32 ≤ 728) : MemoryWriteFrame t u #v[Stack.region s 1016] := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a ha
  have covers := copy_covers hc ha
  rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) (by omega)] at covers
  exact ⟨Stack.region s 1016, by simp,
    stack_contains pre (by omega) (by omega) covers⟩

theorem copy_keeps [Bindings] {s t u : RamState} {next : BitVec 64} {src : BitVec 5}
    {source target offset x : Nat} (state : FrameState s t 96 1016 728)
    (effect : (copyEffect next src source target t).Holds t u)
    (bound : target+32 ≤ 728) (offbound : offset ≤ 728) (offend : 32 ≤ offset)
    (apart : target+32 ≤ 728-offset ∨ 728-offset+32 ≤ target)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) x) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) x := by
  refine ⟨input.1, input.2.1, fun i hi => ?_⟩
  rw [effect.agrees.byte]
  · exact input.2.2 i hi
  · intro c hc ha
    have cover := copy_covers hc ha
    obtain ⟨j, hj, he⟩ := cover
    have addr : stackPtr s - BitVec.ofNat 64 offset = stackPtr t + BitVec.ofNat 64 (728-offset) := by
      rw [scalar_stack_address (frameOffset := 728) state.rsp (by decide) (by omega)]
      congr 2
      omega
    rw [addr] at he
    exact RangeApart.offsets (stackPtr t) (by omega) (by omega) apart j hj i hi he.symm

theorem copy_limb_bound (i : BitVec 64) (hi : i ∈ ([0,8,16,24] : List (BitVec 64))) : i.toNat ≤ 24 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> decide

theorem point_copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p : BitVec 64} {source target : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = p) (rbx : t.regValue .rbx = s.regValue .rdi)
    (srcbound : source+32 ≤ 96) (dstbound : target+32 ≤ 728) :
    CopyPre p 3 source target t := by
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have bound := copy_limb_bound i hi
    change MemReadable t (t.regValue .rbx + BitVec.ofNat 64 source+i) 8
    rw [rbx]
    simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, stackPtr, Operand.read_reg64] using
      point_readable pre state (offset := source+i.toNat) (len := 8) (by omega)
  · intro i hi
    have bound := copy_limb_bound i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, stackPtr, Operand.read_reg64] using
      stack_writable (frameOffset := 728) pre state (by decide) (offset := target+i.toNat) (len := 8) (by omega) (by decide)
  · change RangeApart (stackPtr t + BitVec.ofNat 64 target) 32
      (t.regValue .rbx + BitVec.ofNat 64 source) 32
    rw [rbx, state.rsp]
    exact stack_point_apart pre dstbound srcbound
  · intro i hi codeOffset codeLen codeBound
    have bound := copy_limb_bound i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, stackPtr, Operand.read_reg64] using
      stack_code (frameOffset := 728) pre state (by decide) (offset := target+i.toNat) (len := 8) (by omega) codeBound

theorem stack_copy_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p : BitVec 64} {source target : Nat}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = p) (srcbound : source+32 ≤ 728) (dstbound : target+32 ≤ 728)
    (apart : target+32 ≤ source ∨ source+32 ≤ target) :
    CopyPre p 4 source target t := by
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have bound := copy_limb_bound i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, stackPtr, Operand.read_reg64] using
      stack_readable (frameOffset := 728) pre state (by decide) (offset := source+i.toNat) (len := 8) (by omega)
  · intro i hi
    have bound := copy_limb_bound i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, stackPtr, Operand.read_reg64] using
      stack_writable (frameOffset := 728) pre state (by decide) (offset := target+i.toNat) (len := 8) (by omega) (by decide)
  · exact RangeApart.offsets (stackPtr t) (by omega) (by omega) apart
  · intro i hi codeOffset codeLen codeBound
    have bound := copy_limb_bound i hi
    simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, stackPtr, Operand.read_reg64] using
      stack_code (frameOffset := 728) pre state (by decide) (offset := target+i.toNat) (len := 8) (by omega) codeBound

end P256.Proofs.Projective.Double.Output
