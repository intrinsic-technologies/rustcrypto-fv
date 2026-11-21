import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Program.ScalarFrame.Choice
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem choice_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (second : Bool)
    (rip : t.RIP = if second then 0x10db6b else 0x10dabe) :
    ∃ u, Advances boundary 6 t u ∧ Frame s u ∧
      u.RIP = (if second then 0x10db70 else 0x10dac3) ∧
      u.regValue .rax = ((t.regValue .rdi).setWidth 8).setWidth 64 ∧
      AgreesExcept (choiceClobbers s 1176) t u := by
  let offset : Nat := if second then 0xdb6b else 0xdabe
  let disp : BitVec 32 := if second then 0xb500 else 0xb5ad
  obtain ⟨u,run,ready,sp,ip,rax,ag⟩ := choice_step pre.toCalleePre
    (frameOffset := 1176) (by decide) (by decide)
    (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated state.rsp offset disp (by cases second <;> decide)
    (by cases second <;> decide +kernel) (by cases second <;> decide +kernel)
    (by cases second <;> exact rip)
  have narrow : AgreesExcept [.reg 0,.flags,.rip,.mem (stackPtr s-1184) 8,
      .mem (stackPtr s-1185) 1] t u := by
    apply ag.narrow
    intro c hc hn
    simp only [choiceClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact sp | exact (hn (by simp)).elim
  have writes : WritesWithin [.reg 0,.flags,.rip,.mem (stackPtr s-1184) 8,
      .mem (stackPtr s-1185) 1] #v[registerRegion s .rdi 24,workRegion s 9992] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s 9992,by simp,
      work_contains pre.toCalleePre (by decide) (by decide) ha⟩
  refine ⟨u,run,state.after_effect pre.toCalleePre (by decide) ready narrow writes
    (by simp),?_,rax,ag⟩
  cases second <;> exact ip

end P256.Proofs.Verifying.Core.Prepare
