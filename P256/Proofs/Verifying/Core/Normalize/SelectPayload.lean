import P256.Proofs.Verifying.Core.Normalize.SelectFacts
import P256.Proofs.Projective.Preserve
import P256.Proofs.Field.Inverse.Tail.Support

set_option autoImplicit false
set_option maxRecDepth 4000

namespace P256.Proofs.Verifying.Core.Normalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

theorem select_setup_zero [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s u) (sp : stackPtr u = stackPtr t)
    (effect : (selectSetupEffect t).Holds t u) :
    Field.MontgomeryAt u (stackPtr t + 864) 0 := by
  refine ⟨by decide,?_⟩
  simp only [Nat.zero_mul,Nat.zero_mod]
  apply Field.Inverse.nat256At_zero_limbs
  · have hr := stack_readable (frameOffset := 1176) pre.toCalleePre state
      (offset := 864) (len := 32) (by decide) (by decide)
    rw [sp] at hr
    exact hr.mem
  · have values := effect.writes
    simp only [selectSetupEffect,Write.AllHold] at values
    have h0 : memLoad u.external (stackPtr t + 864#64) 64 = 0#64 := values.2.2.2.1
    have h1 : memLoad u.external (stackPtr t + 872#64) 64 = 0#64 := values.2.2.1
    have h2 : memLoad u.external (stackPtr t + 880#64) 64 = 0#64 := values.2.1
    have h3 : memLoad u.external (stackPtr t + 888#64) 64 = 0#64 := values.1
    change memLoad u.external (stackPtr t + 864#64 + 0#64) 64 = 0#64 ∧
      memLoad u.external (stackPtr t + 864#64 + 8#64) 64 = 0#64 ∧
      memLoad u.external (stackPtr t + 864#64 + 16#64) 64 = 0#64 ∧
      memLoad u.external (stackPtr t + 864#64 + 24#64) 64 = 0#64
    simpa only [BitVec.add_assoc,BitVec.reduceAdd] using And.intro h0 ⟨h1,h2,h3⟩

theorem select_setup_preserved [Bindings] {s t u : RamState} {offset len : Nat}
    (state : Frame s t) (effect : (selectSetupEffect t).Holds t u)
    (bound : offset ≤ 1176)
    (apart : ∀ k < 4, OffsetsApart (BitVec.ofNat 64 (864+8*k)) 8
      (BitVec.ofNat 64 (1176-offset)) len) (small : 8+len < 2^64) :
    ∀ i < len, u.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  have address : stackPtr t + BitVec.ofNat 64 (1176-offset) =
      stackPtr s-BitVec.ofNat 64 offset := by
    have h := scalar_stack_address (frameOffset := 1176) state.rsp
      (offset := 1176-offset) (by decide) (by omega)
    rwa [Nat.sub_sub_self bound] at h
  intro i hi
  have h := select_setup_bytes effect apart small i hi
  rwa [address] at h

structure SelectReady [Bindings] (s t : RamState) (point : Projective) (r : Nat) : Prop
    extends Frame s t where
  rip : t.RIP = 0x10dea5
  represented : ProjectiveAt t (stackPtr s-1176) point
  scalar : Nat256At t (stackPtr s-472) r
  inverse : Field.MontgomeryAt t (stackPtr s-280) (Curve.inverse Operations.domain.p point.z)
  zero : Field.MontgomeryAt t (stackPtr s-312) 0
  rbp : (t.regValue .rbx).setWidth 8 = if point.z=0 then 0 else 1
  choice : (t.regValue .rcx).setWidth 8 = if point.z=0 then 0 else 1
  r14 : t.regValue .r14 = stackPtr s-80
  left : t.regValue .rsi = stackPtr s-312
  right : t.regValue .rdx = stackPtr s-280
  output : t.regValue .rdi = stackPtr s-80

set_option maxHeartbeats 800000 in
theorem select_prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {r : Nat} (pre : Core.Pre s boundary) (state : Frame s t)
    (rip : t.RIP = 0x10de56) (pointAt : ProjectiveAt t (stackPtr s-1176) point)
    (rAt : Nat256At t (stackPtr s-472) r)
    (inverseAt : Field.MontgomeryAt t (stackPtr s-280) (Curve.inverse Operations.domain.p point.z))
    (flag : t.external[stackPtr s-248]? = some (if point.z=0 then 0 else 1))
    (saved : t.regValue .r15 = stackPtr s-280) :
    ∃ n u, Advances boundary n t u ∧ SelectReady s u point r ∧
      memLoad u.external (stackPtr s-792) 64 = memLoad t.external (stackPtr s-792) 64 := by
  obtain ⟨n,u,run,frame,effect⟩ := select_setup pre state rip
  have pointNext : ProjectiveAt u (stackPtr s-1176) point := by
    apply pointAt.of_bytes_eq
    intro i hi
    exact select_setup_preserved state effect (offset := 1176) (len := 96) (by decide)
      (by
        intro k hk
        have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
        rcases h with rfl|rfl|rfl|rfl <;> unfold OffsetsApart <;> decide +kernel)
      (by decide) i hi
  have rNext : Nat256At u (stackPtr s-472) r := ⟨rAt.1,fun i hi =>
    (select_setup_preserved state effect (offset := 472) (len := 32) (by decide)
      (by
        intro k hk
        have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
        rcases h with rfl|rfl|rfl|rfl <;> unfold OffsetsApart <;> decide +kernel) (by decide) i hi).trans (rAt.2 i hi)⟩
  have inverseNext : Field.MontgomeryAt u (stackPtr s-280)
      (Curve.inverse Operations.domain.p point.z) := by
    apply inverseAt.of_bytes_eq
    intro i hi
    exact select_setup_preserved state effect (offset := 280) (len := 32) (by decide)
      (by
        intro k hk
        have h : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
        rcases h with rfl|rfl|rfl|rfl <;> unfold OffsetsApart <;> decide +kernel)
      (by decide) i hi
  have zeroNext := select_setup_zero pre frame (frame.rsp.trans state.rsp.symm) effect
  have zeroAddress : stackPtr t+864 = stackPtr s-312 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  rw [zeroAddress] at zeroNext
  have flagAddress : stackPtr t+928 = stackPtr s-248 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have flags := select_setup_choice effect (flagAddress ▸ flag)
  have values := effect.writes
  simp only [selectSetupEffect,Write.AllHold] at values
  have outAddress : stackPtr t+1096 = stackPtr s-80 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  refine ⟨n,u,run,⟨frame,effect.rip,pointNext,rNext,inverseNext,zeroNext,?_,?_,
    values.2.2.2.2.2.1.trans outAddress,values.2.2.2.2.2.2.1.trans zeroAddress,
    values.2.2.2.2.2.2.2.2.1.trans saved,values.2.2.2.2.2.2.2.1.trans outAddress⟩,?_⟩
  · by_cases hz : point.z=0 <;> simpa [hz] using flags.1
  · by_cases hz : point.z=0 <;> simpa [hz] using flags.2
  · apply memLoad_congr
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    congr 1
    exact select_setup_preserved state effect (offset := 792) (len := 8) (by decide)
      (by intro k hk
          rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl|rfl|rfl|rfl
          all_goals unfold OffsetsApart; decide +kernel) (by decide) i hi

end P256.Proofs.Verifying.Core.Normalize
