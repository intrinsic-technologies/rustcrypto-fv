import P256.Proofs.Projective.Multiply.Machine.Lookup.Memory
import P256.Proofs.Program.ScalarFrame.Choice

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem choice_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (codeOffset : Nat) (disp : BitVec 32) (codeBound : codeOffset + 5 < 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5
      (disp.signExtend 64) = 0x119070)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (5 : BitVec 64) ∧
      u.regValue .rax = ((t.regValue .rdi).setWidth 8).setWidth 64 ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ offset len : Nat, offset ≤ 360 → len ≤ offset + 8 →
        ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
          t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) := by
  obtain ⟨u,run,ready,sp,ip,rax,ag⟩ := ScalarFrame.choice_step pre
    (frameOffset := 360) (by decide) (by decide) (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated state.rsp codeOffset disp codeBound bytes target rip
  have narrow : AgreesExcept [.reg 0,.flags,.rip,.mem (stackPtr s-368) 8,
      .mem (stackPtr s-369) 1] t u := by
    apply ag.narrow
    intro c hc hn
    simp only [ScalarFrame.choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0,.flags,.rip,.mem (stackPtr s-368) 8,
      .mem (stackPtr s-369) 1] #v[registerRegion s .rdi 96,workRegion s] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s,by simp,work_contains pre (by decide) (by decide) ha⟩
  refine ⟨6,u,run,after pre state ready narrow writes (by simp),ip,rax,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
    · exact narrow.read (n := 64) (r := 3) (by simp)
    · exact narrow.read (n := 64) (r := 5) (by simp)
    · exact narrow.read (n := 64) (r := 12) (by simp)
    · exact narrow.read (n := 64) (r := 13) (by simp)
    · exact narrow.read (n := 64) (r := 14) (by simp)
    · exact narrow.read (n := 64) (r := 15) (by simp)
  · intro offset len bound endBound i hi
    apply narrow.byte
    intro c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨j,hj,eq⟩ := ha
    all_goals
      have hb := stack_bounds pre.stack
      have ho := stack_sub_toNat pre.stack (offset := offset) (by omega)
      have hm := stack_sub_toNat pre.stack (offset := 368) (by decide)
      have hn := stack_sub_toNat pre.stack (offset := 369) (by decide)
      have he := congrArg BitVec.toNat eq
      rw [toNat_add_ofNat _ _ (by rw [ho]; omega),ho] at he
      have hm' : (stackPtr s - (368 : BitVec 64)).toNat = (stackPtr s).toNat - 368 := hm
      have hn' : (stackPtr s - (369 : BitVec 64)).toNat = (stackPtr s).toNat - 369 := hn
      first
      | rw [toNat_add_ofNat _ _ (by rw [hm']; omega),hm'] at he; omega
      | rw [toNat_add_ofNat _ _ (by rw [hn']; omega),hn'] at he; omega

end P256.Proofs.Projective.Multiply.Machine.Lookup
