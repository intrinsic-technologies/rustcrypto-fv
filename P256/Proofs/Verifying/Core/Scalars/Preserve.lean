import P256.Proofs.Verifying.Core.Scalars.FirstSetup.Run
import P256.Proofs.Verifying.Core.Scalars.SecondSetup.Run
import P256.Proofs.Verifying.Core.Scalars.InverseGuard
import P256.Proofs.Verifying.Core.Prepare.Pointers

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open Prelude X86 X86.Machine X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem first_slot {s t u : RamState} {offset x : Nat}
    (rsp : rspOf t = frameBase s) (effect : (FirstSetup.Block.effect t).Holds t u)
    (low : 160 ≤ offset) (high : offset+32 ≤ 1128)
    (apart : offset+32 ≤ 768 ∨ 800 ≤ offset)
    (value : Nat256At t (frameBase s+BitVec.ofNat 64 offset) x) :
    Nat256At u (frameBase s+BitVec.ofNat 64 offset) x := by
  refine ⟨value.1,fun i hi => ?_⟩
  rw [effect.agrees.byte]
  · exact value.2 i hi
  · intro c hc covered
    simp only [FirstSetup.Block.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,eq⟩ := covered
    all_goals rw [rsp] at eq
    all_goals bv_omega

theorem second_slot {s t u : RamState} {offset x : Nat}
    (rsp : rspOf t = frameBase s) (effect : (SecondSetup.Block.effect t).Holds t u)
    (low : 160 ≤ offset) (high : offset+32 ≤ 1128)
    (value : Nat256At t (frameBase s+BitVec.ofNat 64 offset) x) :
    Nat256At u (frameBase s+BitVec.ofNat 64 offset) x := by
  refine ⟨value.1,fun i hi => ?_⟩
  rw [effect.agrees.byte]
  · exact value.2 i hi
  · intro c hc covered
    simp only [SecondSetup.Block.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,eq⟩ := covered
    all_goals rw [rsp] at eq
    all_goals bv_omega

theorem guard_slot {s t u : RamState} {offset x : Nat}
    (agrees : AgreesExcept [.reg 0,.mem (frameBase s+0) 1,.flags,.rip] t u)
    (low : 1 ≤ offset) (high : offset+32 ≤ 1128)
    (value : Nat256At t (frameBase s+BitVec.ofNat 64 offset) x) :
    Nat256At u (frameBase s+BitVec.ofNat 64 offset) x := by
  refine ⟨value.1,fun i hi => ?_⟩
  rw [agrees.byte]
  · exact value.2 i hi
  · intro c hc covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    obtain ⟨j,hj,eq⟩ := covered
    bv_omega

theorem slot_address (s : RamState) (offset : Nat) (bound : offset ≤ 1176) :
    frameBase s+BitVec.ofNat 64 offset = stackPtr s-BitVec.ofNat 64 (1176-offset) := by
  unfold frameBase
  bv_omega

theorem call_slot {s t u : RamState} {outOffset outBytes offset x : Nat}
    (bytes : ∀ pos len, pos ≤ 1176 → len ≤ pos+8 →
      (pos+outBytes ≤ outOffset ∨ outOffset+len ≤ pos) → ∀ i < len,
      u.external[stackPtr s-BitVec.ofNat 64 pos+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-BitVec.ofNat 64 pos+BitVec.ofNat 64 i]?)
    (bound : offset ≤ 1128)
    (apart : 1176-offset+outBytes ≤ outOffset ∨ outOffset+32 ≤ 1176-offset)
    (value : Nat256At t (frameBase s+BitVec.ofNat 64 offset) x) :
    Nat256At u (frameBase s+BitVec.ofNat 64 offset) x := by
  rw [slot_address s offset (by omega)] at value ⊢
  exact ⟨value.1,fun i hi => (bytes (1176-offset) 32 (by omega) (by omega) apart i hi).trans
    (value.2 i hi)⟩

theorem pointers_saved {s t u : RamState} (pointers : Prepare.Pointers s t)
    (regs : ∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],u.regValue r=t.regValue r) :
    Prepare.Pointers s u :=
  ⟨(regs .rbx (by simp)).trans pointers.signature⟩

end P256.Proofs.Verifying.Core.Scalars
