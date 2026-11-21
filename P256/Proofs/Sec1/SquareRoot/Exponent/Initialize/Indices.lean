import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prologue
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.Instructions.ByteLogic.And
import P256.Proofs.Common.Instructions.ByteLogic.Unary

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_cl_three_effect_step incClEffect inc_cl_effect_step)

theorem prepare_indices [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (frame : Frame s t)
    (rip : t.RIP=0x1153d4) (count : t.regValue .r14=254) :
    ∃ u, Advances boundary 9 t u ∧ Frame s u ∧ u.RIP=0x1153ee ∧
      u.regValue .rbx=3 ∧ u.regValue .r13=15 ∧ u.regValue .rcx=2 ∧
      AgreesExcept [.reg 1,.reg 3,.reg 13,.flags,.rip] t u := by
  have source1 : t.regValue .r14=254 := count
  obtain ⟨t1,a1,r1,e1⟩ := (mov_r32_r32_rex_effect_step 0x1153d4 0x44 0xf1 (by simp [RexNoWPrefix]) rfl).advances
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0x153d4 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153d7 (by decide)))
  have g1 : AgreesExcept [.reg 1,.rip] t t1 := e1.agrees
  have f1 := frame.after_registers r1 g1 (by simp [Component.Covers]) (by simp)
  have v1 : t1.regValue .rcx=254 := by
    have h : t1.regValue .rcx=((t.regValue .r14).setWidth 32).setWidth 64 := e1.writes
    rw [source1] at h
    exact h
  have source2 : t1.regValue .rcx=254 := v1
  obtain ⟨t2,a2,r2,e2⟩ := (dec_r32_effect_step 0x1153d7 0xc9 rfl rfl).advances
    (readyToStep f1.machine f1.bindingsSupported)
    (programText_slice (programLoaded_codeIn f1.loaded) 0x153d7 _ (by decide) (by decide +kernel))
    e1.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153d9 (by decide)))
  have g2 : AgreesExcept [.reg 1,.flags,.rip] t1 t2 := e2.agrees
  have f2 := f1.after_registers r2 g2 (by simp [Component.Covers]) (by simp)
  have v2 : t2.regValue .rcx=253 := by
    have h : t2.regValue .rcx=((t1.regValue .rcx).setWidth 32 - 1).setWidth 64 := e2.writes
    rw [source2] at h
    exact h
  have source3 : t2.regValue .rcx=253 := v2
  obtain ⟨t3,a3,r3,e3⟩ := (mov_r32_r32_effect_step 0x1153d9 0xcb rfl).advances
    (readyToStep f2.machine f2.bindingsSupported)
    (programText_slice (programLoaded_codeIn f2.loaded) 0x153d9 _ (by decide) (by decide +kernel))
    e2.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153db (by decide)))
  have g3 : AgreesExcept [.reg 3,.rip] t2 t3 := e3.agrees
  have f3 := f2.after_registers r3 g3 (by simp [Component.Covers]) (by simp)
  have v3 : t3.regValue .rbx=253 := by
    have h : t3.regValue .rbx=((t2.regValue .rcx).setWidth 32).setWidth 64 := e3.writes
    rw [source3] at h
    exact h
  have source4 : t3.regValue .rbx=253 := v3
  obtain ⟨t4,a4,r4,e4⟩ := (shr_r32_imm8_effect_step 0x1153db 0xeb 6 rfl rfl).advances
    (readyToStep f3.machine f3.bindingsSupported)
    (programText_slice (programLoaded_codeIn f3.loaded) 0x153db _ (by decide) (by decide +kernel))
    e3.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153de (by decide)))
  have g4 : AgreesExcept [.reg 3,.flags,.rip] t3 t4 := e4.agrees
  have f4 := f3.after_registers r4 g4 (by simp [Component.Covers]) (by simp)
  have v4 : t4.regValue .rbx=3 := by
    have h : t4.regValue .rbx=((t3.regValue .rbx).setWidth 32 >>> 6).setWidth 64 := e4.writes
    rw [source4] at h
    exact h
  have source5 : t4.regValue .rcx=253 := ((g3.trans g4).read (n := 64) (r := 1) (by simp)).trans v2
  obtain ⟨t5,a5,r5,e5⟩ := (mov_r32_r32_rex_effect_step 0x1153de 0x41 0xcd (by simp [RexNoWPrefix]) rfl).advances
    (readyToStep f4.machine f4.bindingsSupported)
    (programText_slice (programLoaded_codeIn f4.loaded) 0x153de _ (by decide) (by decide +kernel))
    e4.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153e1 (by decide)))
  have g5 : AgreesExcept [.reg 13,.rip] t4 t5 := e5.agrees
  have f5 := f4.after_registers r5 g5 (by simp [Component.Covers]) (by simp)
  have v5 : t5.regValue .r13=253 := by
    have h : t5.regValue .r13=((t4.regValue .rcx).setWidth 32).setWidth 64 := e5.writes
    rw [source5] at h
    exact h
  have source6 : t5.regValue .r13=253 := v5
  obtain ⟨t6,a6,r6,e6⟩ := (shr_r32_imm8_rex_effect_step 0x1153e1 0x41 0xed 2 (by simp [RexNoWPrefix]) rfl rfl).advances
    (readyToStep f5.machine f5.bindingsSupported)
    (programText_slice (programLoaded_codeIn f5.loaded) 0x153e1 _ (by decide) (by decide +kernel))
    e5.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153e5 (by decide)))
  have g6 : AgreesExcept [.reg 13,.flags,.rip] t5 t6 := e6.agrees
  have f6 := f5.after_registers r6 g6 (by simp [Component.Covers]) (by simp)
  have v6 : t6.regValue .r13=63 := by
    have h : t6.regValue .r13=((t5.regValue .r13).setWidth 32 >>> 2).setWidth 64 := e6.writes
    rw [source6] at h
    exact h
  have source7 : t6.regValue .r13=63 := v6
  obtain ⟨t7,a7,r7,e7⟩ := (and_r32_imm8_rex_effect_step 0x1153e5 0x41 0xe5 15 (by simp [RexNoWPrefix]) rfl rfl).advances
    (readyToStep f6.machine f6.bindingsSupported)
    (programText_slice (programLoaded_codeIn f6.loaded) 0x153e5 _ (by decide) (by decide +kernel))
    e6.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153e9 (by decide)))
  have g7 : AgreesExcept [.reg 13,.flags,.rip] t6 t7 := e7.agrees
  have f7 := f6.after_registers r7 g7 (by simp [Component.Covers]) (by simp)
  have v7 : t7.regValue .r13=15 := by
    have h : t7.regValue .r13=((t6.regValue .r13).setWidth 32 &&& (15#32)).setWidth 64 := e7.writes
    rw [source7] at h
    exact h
  have source8 : t7.regValue .rcx=253 := (((((g3.trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 1) (by simp)).trans v2
  obtain ⟨t8,a8,r8,e8⟩ := (and_cl_three_effect_step 0x1153e9).advances
    (readyToStep f7.machine f7.bindingsSupported)
    (programText_slice (programLoaded_codeIn f7.loaded) 0x153e9 _ (by decide) (by decide +kernel))
    e7.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153ec (by decide)))
  have g8 : AgreesExcept [.reg 1,.flags,.rip] t7 t8 := e8.agrees
  have f8 := f7.after_registers r8 g8 (by simp [Component.Covers]) (by simp)
  have v8 : t8.regValue .rcx=1 := by
    have h : t8.regValue .rcx=mergeGPR 8 ((t7.regValue .rcx).setWidth 8 &&& (3#8)) (t7.regValue .rcx) := e8.writes
    rw [source8] at h
    exact h
  have source9 : t8.regValue .rcx=1 := v8
  obtain ⟨t9,a9,r9,e9⟩ := (inc_cl_effect_step 0x1153ec).advances
    (readyToStep f8.machine f8.bindingsSupported)
    (programText_slice (programLoaded_codeIn f8.loaded) 0x153ec _ (by decide) (by decide +kernel))
    e8.rip (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x153ee (by decide)))
  have g9 : AgreesExcept [.reg 1,.flags,.rip] t8 t9 := e9.agrees
  have f9 := f8.after_registers r9 g9 (by simp [Component.Covers]) (by simp)
  have v9 : t9.regValue .rcx=2 := by
    have h : t9.regValue .rcx=mergeGPR 8 ((t8.regValue .rcx).setWidth 8 + (1#8)) (t8.regValue .rcx) := e9.writes
    rw [source9] at h
    exact h
  refine ⟨t9,((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9),f9,e9.rip,?_,?_,v9,?_⟩
  · exact (((((g5.trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 3) (by simp)).trans v4
  · exact ((g8.trans g9).read (n := 64) (r := 13) (by simp)).trans v7
  · exact ((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).mono (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; grind only)

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
