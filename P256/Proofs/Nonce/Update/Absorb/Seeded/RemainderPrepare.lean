import P256.Proofs.Nonce.Update.Absorb.Seeded.Digest
import P256.Proofs.Nonce.Update.Absorb.Seeded.RemainderHead
import P256.Proofs.Nonce.Update.Absorb.Seeded.RemainderSetup
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem prepare_remainder [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input secret : ByteArray} {address : BitVec 64}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (compressed : Compressed initial s state input secret address) :
    ∃ fuel t, Advances boundary fuel s t ∧ RemainderReady initial t state input secret address := by
  have hp : RemainderHead.Pre s := ⟨compressed.rip,compressed.remaining,
    stack_writable1 pre compressed.toFrameState (by decide),fun pc len bound =>
      ScalarFrame.stack_code pre.callee compressed.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨headFuel,u,headRun,readyU,_,head⟩ := RemainderHead.run boundary pre.outerBoundary s
    (readyToStep compressed.machine compressed.bindingsSupported) (RemainderHead.code compressed.loaded) hp
  have headAgrees : AgreesExcept [.mem (scratch initial + 215) 1,.reg 12,.reg 2,.flags,.rip] s u := by
    have h := head.agrees
    simp only [RemainderHead.effect,Effect.components,List.map,Write.component,Operand.component] at h
    rwa [show rspOf s = scratch initial from compressed.rsp] at h
  have digestU := compressed.toDigest.step_position pre readyU headAgrees (by simp) (by simp) (by simp) (by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact cover
    all_goals exact cover.elim)
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = true := head.flags.2.2.2.1
  obtain ⟨v,branchStep,readyV,branch⟩ := jcc_rel8_effect_step 0x10a332 4 0x18 u readyU
    (programText_slice (programLoaded_codeIn digestU.loaded) 0xa332 _ (by decide) (by decide +kernel))
    ⟨head.rip,by intro; decide⟩
  have ripV : v.RIP = 0x10a34c := by
    rw [branch.rip]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then 0x10a34c else 0x10a334) = _
    simp only [zero,↓reduceIte]
  have branchRun : Advances boundary 1 u v := Advances.of_step branchStep (.inl (by
    rw [ripV]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa34c (by decide))))
  have branchAgrees : AgreesExcept [.rip] u v := branch.agrees
  have digestV := digestU.step_position pre readyV branchAgrees (by simp) (by simp) (by simp)
    (by simp [Component.Covers])
  have remaining : v.regValue .rbx = 1 :=
    ((headAgrees.trans branchAgrees).read (n:=64) (r:=3) (by simp)).trans compressed.remaining
  have sourceU : u.regValue .r12 = address + 31 := by
    have h := head.writes
    change memLoad u.external (stackPtr s + 215) 8 = 0 ∧
      u.regValue .r12 = s.regValue .r15 ∧ u.regValue .rdx = 0 at h
    exact h.2.1.trans compressed.tail
  have sourceV : v.regValue .r12 = address + 31 :=
    (branchAgrees.read (n:=64) (r:=12) (by simp)).trans sourceU
  have setupPre : RemainderSetup.Pre v := ⟨ripV,remaining,
    stack_writable1 pre digestV.toFrameState (by decide),fun pc len bound =>
      ScalarFrame.stack_code pre.callee digestV.toFrameState (by decide) (by decide) bound⟩
  obtain ⟨setupFuel,t,setupRun,readyT,_,setup⟩ := RemainderSetup.run boundary pre.outerBoundary v readyV
    (RemainderSetup.code digestV.loaded) setupPre
  have setupAgrees : AgreesExcept [.reg 0,.reg 1,.reg 3,.reg 12,.mem (scratch initial + 215) 1,
      .reg 7,.reg 6,.reg 2,.flags,.rip] v t := by
    have h := setup.agrees
    simp only [RemainderSetup.effect,Effect.components,List.map,Write.component,Operand.component] at h
    rwa [show rspOf v = scratch initial from digestV.rsp] at h
  have digestT := digestV.step_position pre readyT setupAgrees (by simp) (by simp) (by simp) (by
    intro c hc a cover
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact cover | exact cover.elim)
  have stores := setup.writes
  change t.regValue .rax = 0 ∧ t.regValue .rcx = 0x7fffffffffffffc0 ∧ t.regValue .rbx = 1 ∧
    t.regValue .r12 = v.regValue .r12 ∧ memLoad t.external (stackPtr v + 215) 8 = 1 ∧
    t.regValue .rdi = stackPtr v + 152 ∧ t.regValue .rsi = v.regValue .r12 ∧
    t.regValue .rdx = 1 at stores
  rw [sourceV,digestV.rsp] at stores
  refine ⟨headFuel+1+setupFuel,t,(headRun.trans branchRun).trans setupRun,
    digestT,setup.rip,stores.2.2.2.2.2.2.1,stores.2.2.2.2.2.1,stores.2.2.2.2.2.2.2,?_⟩
  apply scratch_byte_of_load pre digestT.toFrameState 215 (by decide) (1 : BitVec 8)
  exact stores.2.2.2.2.1

end P256.Proofs.Nonce.Update.Absorb.Seeded
