import P256.Proofs.Nonce.Update.Seeded.Absorb.Digest
import P256.Proofs.Nonce.Update.Seeded.Absorb.RemainderHead
import P256.Proofs.Nonce.Update.Seeded.Absorb.RemainderSetup

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Update.Absorb
open Update.Absorb.Seeded (scratch_byte_of_load)

theorem prepare_remainder [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {original state : State} {input secret : ByteArray} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (compressed : Compressed initial s state input secret address) :
    ∃ fuel t, Advances boundary fuel s t ∧ RemainderReady initial t state input secret address := by
  have hp : RemainderHead.Pre s := ⟨compressed.rip,compressed.remaining,
    stack_writable1 pre compressed.toFrameState (by decide),fun pc len bound =>
      ScalarFrame.stack_code pre.callee compressed.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨headFuel,u,headRun,readyU,_,head⟩ := RemainderHead.run boundary pre.outerBoundary s
    (readyToStep compressed.machine compressed.bindingsSupported) (RemainderHead.code compressed.loaded) hp
  have headAgrees : AgreesExcept [.mem (scratch initial + 383) 1,.reg 6,.reg 2,.flags,.rip] s u := by
    have h := head.agrees
    simp only [RemainderHead.branchEffect,RemainderHead.effect,Effect.components,List.map,Write.component,Operand.component] at h
    rwa [show rspOf s = scratch initial from compressed.rsp] at h
  have digestU := compressed.toDigest.step_position pre readyU headAgrees (by simp) (by simp) (by simp) (by simp) (by simp) (by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact cover
    all_goals exact cover.elim)
  have remaining : u.regValue .r15 = 1 :=
    (headAgrees.read (n:=64) (r:=15) (by simp)).trans compressed.remaining
  have sourceU : u.regValue .rsi = address + 31 := by
    have h := head.writes
    change memLoad u.external (stackPtr s + 383) 8 = 0 ∧
      u.regValue .rsi = s.regValue .rbx ∧ u.regValue .rdx = 0 at h
    exact h.2.1.trans compressed.tail
  have setupPre : RemainderSetup.Pre u := ⟨head.rip,remaining,
    stack_writable1 pre digestU.toFrameState (by decide),fun pc len bound =>
      ScalarFrame.stack_code pre.callee digestU.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨setupFuel,t,setupRun,readyT,_,setup⟩ := RemainderSetup.run boundary pre.outerBoundary u readyU
    (RemainderSetup.code digestU.loaded) setupPre
  have setupAgrees : AgreesExcept [.reg 0,.reg 1,.reg 15,.reg 6,.mem (scratch initial + 383) 1,
      .reg 7,.reg 2,.flags,.rip] u t := by
    have h := setup.agrees
    simp only [RemainderSetup.effect,Effect.components,List.map,Write.component,Operand.component] at h
    rwa [show rspOf u = scratch initial from digestU.rsp] at h
  have digestT := digestU.step_position pre readyT setupAgrees (by simp) (by simp) (by simp) (by simp) (by simp) (by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact cover | exact cover.elim)
  have stores := setup.writes
  change t.regValue .rax = 0 ∧ t.regValue .rcx = 0x7fffffffffffffc0 ∧ t.regValue .r15 = 1 ∧
    t.regValue .rsi = u.regValue .rsi ∧ memLoad t.external (stackPtr u + 383) 8 = 1 ∧
    t.regValue .rdi = u.regValue .r12 ∧ t.regValue .rdx = 1 at stores
  rw [sourceU,digestU.rsp,digestU.bufferPointer] at stores
  refine ⟨headFuel+setupFuel,t,headRun.trans setupRun,
    digestT,setup.rip,stores.2.2.2.1,stores.2.2.2.2.2.1,stores.2.2.2.2.2.2,?_⟩
  apply scratch_byte_of_load pre digestT.toFrameState 383 (by decide) (1 : BitVec 8)
  exact stores.2.2.2.2.1

end P256.Proofs.Nonce.Update.Seeded.Absorb
