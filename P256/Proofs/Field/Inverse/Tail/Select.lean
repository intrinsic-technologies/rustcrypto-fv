import P256.Proofs.Field.Inverse.Tail.SelectResult

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def selectCallOffset (second : Bool) : Nat := if second then 0x141ff else 0x14196

def selectDisplacement (second : Bool) : BitVec 32 := if second then 0x4fbc else 0x5025

theorem select_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {source : Nat} {select : Bool}
    (pre : Pre s boundary) (state : SelectCallState s t source select)
    (second : Bool) (rip : t.RIP = (0x100000 : BitVec 64) + BitVec.ofNat 64 (selectCallOffset second)) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (callEffect (fun _ => 0x1191c0)
        ((0x100000 : BitVec 64) + BitVec.ofNat 64 (selectCallOffset second) + 5#64) t).Holds t u := by
  have target : branchTarget ((0x100000 : BitVec 64) + BitVec.ofNat 64 (selectCallOffset second)) 5
      ((selectDisplacement second).signExtend 64) = 0x1191c0 := by
    cases second <;> decide +kernel
  have code := programText_slice (programLoaded_codeIn state.loaded)
    (selectCallOffset second) (encodeCallRel32 (selectDisplacement second))
    (by cases second <;> decide +kernel) (by cases second <;> decide +kernel)
  have hpush : PushPre ((0x100000 : BitVec 64) + BitVec.ofNat 64 (selectCallOffset second)) 5 t := by
    refine ⟨rip, ?_, ?_⟩
    · rw [select_call_address state]
      exact P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable8 pre.stack (fun a ha ht ↦ pre.avoids _ (by simp) a ha (.inr ht))
        (by decide) (by decide)) state.allocated
    · rw [select_call_address state]
      exact stack_code_apart pre (codeOffset := selectCallOffset second)
        (by decide) (by decide) (by cases second <;> decide)
  simpa only [target] using
    (call_rel32_effect_step ((0x100000 : BitVec 64) + BitVec.ofNat 64 (selectCallOffset second))
      (selectDisplacement second) (by rw [target]; decide)).advances
      (readyToStep state.machine state.bindingsSupported) code hpush
      (by
        rw [target]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0x191c0 (by decide)))

theorem select_stage [Bindings] {s t : RamState} {boundary : ReturnBoundary} {source beta : Nat} {select : Bool}
    (pre : Pre s boundary) (state : SelectCallState s t source select)
    (hsource : 48 ≤ source ∧ source ≤ 136)
    (second : Bool) (rip : t.RIP = (0x100000 : BitVec 64) + BitVec.ofNat 64 (selectCallOffset second))
    (candidate : Nat256At t (stackPtr s - BitVec.ofNat 64 (if select then source else 168)) beta) :
    ∃ n u, Advances boundary n t u ∧ FrameState s u ∧
      u.RIP = (0x100000 : BitVec 64) + BitVec.ofNat 64 (selectCallOffset second) + 5#64 ∧
      u.regValue .rbp = (if select then 1 else 0) ∧ Nat256At u (stackPtr s - 168) beta := by
  obtain ⟨t1, run1, ready1, effect1⟩ := select_call pre state second rip
  have hret : InProgram ((0x100000 : BitVec 64) + BitVec.ofNat 64 (selectCallOffset second) + 5#64) := by
    cases second
    · exact inProgram_of_textOffset 0x1419b (by decide)
    · exact inProgram_of_textOffset 0x14204 (by decide)
  obtain ⟨n, u, run2, state2, rip2, rbp2, output⟩ :=
    select_result pre state hsource hret ready1 effect1 candidate
  exact ⟨1+n, u, run1.trans run2, state2, rip2, rbp2, output⟩

end P256.Proofs.Field.Inverse
