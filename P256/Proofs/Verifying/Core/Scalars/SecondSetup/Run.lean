import P256.Proofs.Verifying.Core.Scalars.SecondSetup.Pre

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars.SecondSetup

open P256.Spec.Program P256.Spec.Program.Routines Prelude Block
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem local_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) :
    WritesWithin (effect t).components #v[workRegion s 9992] := by
  intro c hc a covered
  simp only [effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals exact ⟨workRegion s 9992,by simp,
    local_work_contains hp state (by decide) covered⟩

theorem prefix_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) :
    WritesWithin (effect t).components (prefixRegions s) := by
  intro c hc a covered
  simp only [effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals exact prefix_local_contains hp state (by decide) covered

set_option maxHeartbeats 800000 in
theorem copy [Bindings] {s u : RamState} {boundary : ReturnBoundary} {r : Nat}
    (hp : Core.Pre s boundary) (state : Frame s u)
    (rip : u.RIP = 0x10dd1d) (r15 : u.regValue .rbx = s.regValue .r8)
    (input : Nat256At u (s.regValue .r8) r) :
    ∃ n t, Advances boundary n u t ∧ Frame s t ∧ (effect u).Holds u t ∧
      Nat256At t (stackPtr s-1048#64) r ∧
      MemoryWriteFrame u t (prefixRegions s) := by
  obtain ⟨n,t,run,ready,_,he⟩ := block boundary
    (fun i hi => by
      have addr : (0x10dd1d : BitVec 64)+BitVec.ofNat 64 i =
          Extracted.textAddress+BitVec.ofNat 64 (0xdd1d+i) := by
        rw [BitVec.ofNat_add,← BitVec.add_assoc]
        rfl
      rw [addr]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    u (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xdd1d bytes
      (by decide) extracted_bytes) (pre hp state rip r15)
  have st := state.after_effect hp.toCalleePre (by decide) ready he.agrees (by
    intro c hc a ha
    obtain ⟨region,hr,hin⟩ := local_writes hp state c hc a ha
    exact ⟨region,by simpa using Or.inr hr,hin⟩) (by simp [effect,Effect.components])
  have hw := he.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_,_,_,_,_,h0,h1,h2,h3⟩
  have ptr : (Operand.reg 3#5 : Operand 64).read u = s.regValue .r8 := r15
  have sp : rspOf u = stackPtr s-1176#64 := state.rsp
  simp only [Write.AllHold,sp,ptr] at h0 h1 h2 h3
  have dst : stackPtr s-1176#64+128#64 = stackPtr s-1048#64 := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  refine ⟨n,t,run,st,he,?_,he.agrees.memoryWriteFrame (prefix_writes hp state)⟩
  apply nat256At_of_memLoad_limbs input.1
  · have h := (stack_readable (frameOffset := 1176) hp.toCalleePre st
      (offset := 128) (len := 32) (by decide) (by decide)).mem
    simpa only [st.rsp,dst] using h
  · intro k hk
    have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl
    · change memLoad t.external (stackPtr s-1048#64+0#64) 64 = _
      rw [BitVec.add_zero,← dst]
      apply h0.trans
      change memLoad u.external (s.regValue .r8) 64 = _
      simpa only [BitVec.ofNat_eq_ofNat,Nat.reduceMul,BitVec.add_zero] using
        input.memLoad_limb 0 (by decide)
    · change memLoad t.external (stackPtr s-1048#64+8#64) 64 = _
      rw [← dst,BitVec.add_assoc]
      exact h1.trans (input.memLoad_limb 1 (by decide))
    · change memLoad t.external (stackPtr s-1048#64+16#64) 64 = _
      rw [← dst,BitVec.add_assoc]
      exact h2.trans (input.memLoad_limb 2 (by decide))
    · change memLoad t.external (stackPtr s-1048#64+24#64) 64 = _
      rw [← dst,BitVec.add_assoc]
      exact h3.trans (input.memLoad_limb 3 (by decide))

end P256.Proofs.Verifying.Core.Scalars.SecondSetup
