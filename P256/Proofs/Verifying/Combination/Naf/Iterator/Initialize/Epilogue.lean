import P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize.Body
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program (pop_register_effect_step readable_of_grow stack_sub_readable)

theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary} {n reserve : Nat}
    (pre : CalleePre s boundary 0x118290 32 40 reserve) (reserved : 24 ≤ reserve)
    (state : BodyState s t n reserve) (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 40 reserve ∧ u.external = t.external ∧
      u.regValue .rax = s.regValue .rdi := by
  have loaded := programLoaded_codeIn state.loaded
  have read (offset : Nat) (ho : offset ≤ 24) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) state.agrees.grow
  obtain ⟨t1, run1, ready1, e1⟩ :=
    (add_r64_imm8_effect_step 0x1182df 0x48 0xc4 8
      (by simp [RexWPrefix]) rfl rfl).advances state.ready
      (programText_slice loaded 0x182df _ (by decide) (by decide +kernel)) state.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x182e3 (by decide)))
  change (addR64Imm8Effect 0x1182df 4 8 t).Holds t t1 at e1
  have mem1 := e1.agrees.external (by simp [Component.Covers])
  have sp1 : stackPtr t1 = stackPtr s - 16#64 := by
    have h : stackPtr t1 = stackPtr t + 8#64 := e1.writes
    rw [h, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have read2 : MemReadable t1 (stackPtr t1) 8 := by
    rw [sp1]
    exact (read 16 (by decide)).of_external_eq mem1
  obtain ⟨t2, run2, ready2, e2⟩ :=
    (pop_register_effect_step 0x1182e3 3 (by decide)).advances ready1
      (programText_slice (loaded.of_external_eq mem1) 0x182e3 _ (by decide) (by decide +kernel))
      ⟨e1.rip, read2⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x182e4 (by decide)))
  have mem2 : t2.external = t.external := (e2.agrees.external (by simp [Component.Covers])).trans mem1
  have sp2 : stackPtr t2 = stackPtr s - 8#64 := by
    have h : stackPtr t2 = stackPtr t1 + 8#64 := e2.writes.2
    rw [h, sp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have rbx : t2.regValue .rbx = s.regValue .rbx := by
    have h : t2.regValue .rbx = memLoad t1.external (stackPtr t1) 64 := e2.writes.1
    rw [h, sp1, mem1]
    exact state.rbx
  have read3 : MemReadable t2 (stackPtr t2) 8 := by
    rw [sp2]
    exact (read 8 (by decide)).of_external_eq mem2
  obtain ⟨t3, run3, ready3, e3⟩ :=
    (pop_register_effect_step 0x1182e4 14 (by decide)).advances ready2
      (programText_slice (loaded.of_external_eq mem2) 0x182e4 _ (by decide) (by decide +kernel))
      ⟨e2.rip, read3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x182e6 (by decide)))
  have mem3 : t3.external = t.external := (e3.agrees.external (by simp [Component.Covers])).trans mem2
  have sp3 : stackPtr t3 = stackPtr s := by
    have h : stackPtr t3 = stackPtr t2 + 8#64 := e3.writes.2
    rw [h, sp2]
    simp only [BitVec.sub_add_cancel]
  have r14 : t3.regValue .r14 = s.regValue .r14 := by
    have h : t3.regValue .r14 = memLoad t2.external (stackPtr t2) 64 := e3.writes.1
    rw [h, sp2, mem2]
    exact state.r14
  have read4 : MemReadable t3 (stackPtr t3) 8 := by
    rw [sp3]
    simpa only [BitVec.sub_zero] using (read 0 (by decide)).of_external_eq mem3
  have top : stackTop t3 = (returnBoundary s).rip := by
    change memLoad t3.external (stackPtr t3) 64 = memLoad s.external (stackPtr s) 64
    rw [sp3, mem3]
    exact state.returnAddress
  obtain ⟨u, run4, ready4, e4⟩ := (ret_effect_step 0x1182e6).advances ready3
    (programText_slice (loaded.of_external_eq mem3) 0x182e6 _ (by decide) (by decide +kernel))
    ⟨⟨e3.rip, read4⟩, top ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t3 ≠ boundary.rip
        rw [top]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have tailAg := ((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees
  have finalAg := state.agrees.trans tailAg
  have memory : u.external = t.external :=
    (e4.agrees.external (by simp [Component.Covers])).trans mem3
  obtain ⟨fuel, run⟩ := execution
  refine ⟨u, calleeResult_of_advances pre
    ((((run.trans run1).trans run2).trans run3).trans run4) ready4 finalAg
    (e4.rip.trans top) ?_ ?_ ?_, memory, ?_⟩
  · change stackPtr u = stackPtr s + 8#64
    have h : stackPtr u = stackPtr t3 + 8#64 := e4.writes
    rw [h, sp3]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ((e3.agrees.trans e4.agrees).read (n := 64) (r := 3) (by simp)).trans rbx
    · exact finalAg.read (n := 64) (r := 5) (by simp [bodyComponents, saveFrame])
    · exact finalAg.read (n := 64) (r := 12) (by simp [bodyComponents, saveFrame])
    · exact finalAg.read (n := 64) (r := 13) (by simp [bodyComponents, saveFrame])
    · exact (e4.agrees.read (n := 64) (r := 14) (by simp)).trans r14
    · exact finalAg.read (n := 64) (r := 15) (by simp [bodyComponents, saveFrame])
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · exact (tailAg.read (n := 64) (r := 0) (by simp)).trans state.rax

end P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize
