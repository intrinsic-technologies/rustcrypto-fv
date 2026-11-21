import P256.Proofs.Projective.Multiply.Machine.Radix.ReturnAddress
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem radix_return [Bindings] {s t : RamState} {boundary : ReturnBoundary} {fuel : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t)
    (execution : Advances boundary fuel s t) (rip : t.RIP = 0x10ba7f)
    (output : t.regValue .rbx = s.regValue .rdi) :
    ∃ u, CalleeResult s u boundary 65 136 ∧ u.external = t.external ∧
      u.regValue .rax = s.regValue .rdi := by
  obtain ⟨v,movrun,rv,mov⟩ :=
    (mov_r64_r64_effect_step 0x10ba7f 0x48 0xd8 (by simp [RexWPrefix]) rfl).advances state.ready
      (programText_slice (programLoaded_codeIn (state.loaded pre)) 0xba7f _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xba82 (by decide)))
  change (movR64R64Effect 0x10ba7f 0 3 t).Holds t v at mov
  have mv := mov.agrees.external (by simp [movR64R64Effect_components,Component.Covers])
  have lv : ProgramLoaded v := by intro a b hb; rw [mv]; exact state.loaded pre a b hb
  obtain ⟨w,addrun,rw_,add⟩ :=
    (add_r64_imm8_effect_step 0x10ba82 0x48 0xc4 112
      (by simp [RexWPrefix]) rfl rfl).advances rv
      (programText_slice (programLoaded_codeIn lv) 0xba82 _
        (by decide) (by decide +kernel)) mov.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xba86 (by decide)))
  change (addR64Imm8Effect 0x10ba82 4 112 v).Holds v w at add
  have mw := add.agrees.external (by simp [addR64Imm8Effect_components,Component.Covers])
  have spw : stackPtr w = stackPtr s-8 := by
    have h : stackPtr w = stackPtr v+112 := add.writes
    have spv : stackPtr v = stackPtr t := mov.agrees.read (n := 64) (r := 4) (by simp)
    rw [h,spv,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have sw : State s w 8 := state.after_registers pre rw_ (mov.agrees.trans add.agrees)
    (by simp [registers]) (by simp [Component.Covers]) spw
  have readw : MemReadable w (stackPtr w) 8 := by
    rw [spw]
    exact readable_of_grow (stack_sub_readable pre.stack (offset := 8) (by decide)
      (by decide)) sw.agrees.grow
  obtain ⟨p,poprun,rp,pop⟩ := (pop_register_effect_step 0x10ba86 3 (by decide)).advances rw_
    (programText_slice (programLoaded_codeIn (sw.loaded pre)) 0xba86 _
      (by decide) (by decide +kernel)) ⟨add.rip,readw⟩
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xba87 (by decide)))
  change (popR64Effect 0x10ba86 1 3 w).Holds w p at pop
  have spp : stackPtr p = stackPtr s := by
    have h : stackPtr p = stackPtr w+8 := pop.writes.2
    rw [h,spw,BitVec.sub_add_cancel]
  have sp : State s p 0 := sw.after_registers pre rp pop.agrees
    (by simp [registers]) (by simp [Component.Covers]) (by simpa using spp)
  have top : stackTop p = (returnBoundary s).rip := by
    change memLoad p.external (stackPtr p) 64 = memLoad s.external (stackPtr s) 64
    rw [spp]
    exact sp.returnAddress pre
  have readp : MemReadable p (stackPtr p) 8 := by
    rw [spp]
    have h := stack_sub_readable pre.stack (offset := 0) (len := 8) (by decide) (by decide)
    exact readable_of_grow (by simpa using h) sp.agrees.grow
  obtain ⟨u,retrun,ru,ret⟩ := (ret_effect_step 0x10ba87).advances rp
    (programText_slice (programLoaded_codeIn (sp.loaded pre)) 0xba87 [0xc3]
      (by decide) (by decide +kernel))
    ⟨⟨pop.rip,readp⟩,top ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop p ≠ boundary.rip
        rw [top]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have mp := pop.agrees.external (by simp [Component.Covers])
  have mu := ret.agrees.external (by simp [Component.Covers])
  have final := sp.agrees.trans ret.agrees
  have rax : u.regValue .rax = s.regValue .rdi :=
    ((add.agrees.trans pop.agrees).trans ret.agrees).read (n := 64) (r := 0)
      (by simp) |>.trans (mov.writes.trans output)
  refine ⟨u,?_,mu.trans (mp.trans (mw.trans mv)),rax⟩
  refine ⟨⟨fuel+1+1+1+1,(((execution.trans movrun).trans addrun).trans poprun).trans retrun⟩,
    ret.rip.trans top,?_,bindingsSupported_of_ready_agrees pre.bindingsSupported ru final,
    supportedMachine_of_ready_agrees pre.machine ru final,?_,
    final.directionFlagClear (by simp [components,registers]) pre.directionFlag,
    final.mxcsr (by simp [components,registers]),final.fcw (by simp [components,registers]),?_,?_,final.grow⟩
  · have h : u.regValue .rsp = stackPtr p+8 := ret.writes
    rw [h,spp]
    rfl
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · have rbp : p.regValue .rbx = s.regValue .rbx := by
        have h : p.regValue .rbx = memLoad w.external (stackPtr w) 64 := pop.writes.1
        rw [h,spw]
        exact sw.saved
      exact (ret.agrees.read (n := 64) (r := 3) (by simp)).trans rbp
    · exact final.read (n := 64) (r := 5) (by simp [components,registers])
    · exact final.read (n := 64) (r := 12) (by simp [components,registers])
    · exact final.read (n := 64) (r := 13) (by simp [components,registers])
    · exact final.read (n := 64) (r := 14) (by simp [components,registers])
    · exact final.read (n := 64) (r := 15) (by simp [components,registers])
  · intro a ha
    rw [mu]
    exact sp.frame pre a ha
  · intro a b hb
    rw [mu]
    exact sp.loaded pre a b hb

end P256.Proofs.Projective.Multiply.Machine.Radix
