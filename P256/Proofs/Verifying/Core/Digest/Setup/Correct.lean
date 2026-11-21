import P256.Proofs.Verifying.Core.Digest.Setup.Prefix
import P256.Proofs.Verifying.Core.Digest.Setup.Initialize
import P256.Proofs.Verifying.Core.Digest.Setup.State

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Setup

set_option maxHeartbeats 1000000 in
theorem setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dbb2)
    (pointers : Prepare.Pointers s t) :
    ∃ fuel u, Advances boundary fuel t u ∧ Reading s u ∧
      AgreesExcept (setupClobbers s) t u := by
  have byteWritable : MemWritable t (stackPtr t+128) 1 := by
    have addr : stackPtr t+128 = stackPtr s-1048 := by
      rw [state.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [addr]
    exact writable_of_grow (stack_sub_writable pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
      (by decide) (by decide) (by decide) (by omega)) state.allocated
  obtain ⟨a, tagRun, tagReady, tag⟩ :=
    (mov_m8_imm8_effect_step 0x10dbb2 (.sib 4 none 0 (.d32 128))
      (by decide) rfl rfl 1).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xdbb2 _
        (by decide) (by decide +kernel))
      ⟨rip, byteWritable, (stack_code pre.toCalleePre state
        (offset := 128) (len := 1) (codeOffset := 0xdbb2) (codeLen := 8)
        (by decide) (by decide) (by decide))⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xdbba (by decide)))
  have tagWrites : WritesWithin (movM8Imm8Effect 0x10dbb2
      (.sib 4 none 0 (.d32 128)) 1 t).components #v[workRegion s 9992] := by
    intro b hc addr covered
    simp only [movM8Imm8Effect,storeEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component_mem,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl|rfl
    · exact ⟨_,by simp,local_work_contains pre state (by decide) covered⟩
    · exact covered.elim
  have stateA := state.after_effect pre.toCalleePre (by decide) tagReady tag.agrees (by
    intro b hc addr covered
    obtain ⟨region,hr,hin⟩ := tagWrites b hc addr covered
    exact ⟨region,by simpa using Or.inr hr,hin⟩) (by simp [movM8Imm8Effect,storeEffect,Effect.components])
  have prefixPre : PrefixPre a := by
    refine ⟨tag.rip,?_,?_⟩
    · change MemWritable a (stackPtr a+128) 1
      have addr : stackPtr a+128 = stackPtr s-1048 := by
        rw [stateA.rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rw [addr]
      exact writable_of_grow (stack_sub_writable pre.stack
        (fun x hx hp => pre.avoids _ (by simp) x hx (.inr hp))
        (by decide) (by decide) (by decide) (by omega)) stateA.allocated
    · intro off len hc
      exact stack_code pre.toCalleePre stateA (offset := 128) (len := 1) (by decide) (by decide) hc
  obtain ⟨n,b,prefixRun,readyB,_,pref⟩ := prefix_block boundary pre.outerBoundary a
    (readyToStep stateA.machine stateA.bindingsSupported)
    (programText_slice (programLoaded_codeIn stateA.loaded) 0xdbba prefixBytes
      (by decide) (by decide +kernel)) prefixPre
  have prefixWrites : WritesWithin (prefixEffect a).components #v[workRegion s 9992] := by
    intro b hc addr covered
    simp only [prefixEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component_mem,Write.component_reg,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl
    · exact covered.elim
    · exact ⟨_,by simp,local_work_contains pre stateA (by decide) covered⟩
    · exact covered.elim
  have stateB := stateA.after_effect pre.toCalleePre (by decide) readyB pref.agrees (by
    intro b hc addr covered
    obtain ⟨region,hr,hin⟩ := prefixWrites b hc addr covered
    exact ⟨region,by simpa using Or.inr hr,hin⟩) (by simp [prefixEffect,Effect.components])
  have initializePre : InitializePre b := by
    refine ⟨pref.rip,?_,?_,?_,?_⟩
    · exact stack_writable pre.toCalleePre stateB (offset := 576) (len := 4) (by decide) (by decide) (by decide)
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      all_goals exact local_writable8 pre stateB (by decide) (by decide)
    · intro off len hc
      exact stack_code pre.toCalleePre stateB (offset := 576) (len := 4) (by decide) (by decide) hc
    · intro i hi off len hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      all_goals exact stack_code pre.toCalleePre stateB (by decide) (by decide) hc
  obtain ⟨m,u,initRun,readyU,_,init⟩ := initialize_block boundary pre.outerBoundary b
    (readyToStep stateB.machine stateB.bindingsSupported)
    (programText_slice (programLoaded_codeIn stateB.loaded) 0xdbda initializeBytes
      (by decide) (by decide +kernel)) initializePre
  have initWrites : WritesWithin (initializeEffect b).components #v[workRegion s 9992] := by
    intro component hc addr covered
    simp only [initializeEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component_mem,Write.component_reg,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals exact ⟨_,by simp,local_work_contains pre stateB (by decide) covered⟩
  have stateU := stateB.after_effect pre.toCalleePre (by decide) readyU init.agrees (by
    intro component hc addr covered
    obtain ⟨region,hr,hin⟩ := initWrites component hc addr covered
    exact ⟨region,by simpa using Or.inr hr,hin⟩)
    (by simp [initializeEffect,Effect.components])
  have agrees : AgreesExcept (setupClobbers s) t u :=
    ((tag.agrees.trans pref.agrees).trans init.agrees).mono (by
      simp [setupClobbers,movM8Imm8Effect,storeEffect,storeAddrAt,
        prefixEffect,initializeEffect,Effect.components,frameBase,
        show rspOf a = stackPtr s-1176 from stateA.rsp,
        show rspOf b = stackPtr s-1176 from stateB.rsp]
      change stackPtr t+128#64 = stackPtr s-1176#64+128#64
      rw [state.rsp]
      rfl)
  have pointersU := pointers.after agrees (by simp [setupClobbers])
  refine ⟨1+n+m,u,(tagRun.trans prefixRun).trans initRun,
    ⟨stateU,pointersU,init.rip,?_,?_,?_,?_,?_⟩,agrees⟩
  · have h : u.regValue .rdi = stackPtr b+424 := init.writes.2.2.2.2.2.1
    simpa only [stateB.rsp,frameBase,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · have h : u.regValue .rdx = stackPtr b+0 := init.writes.2.2.2.2.2.2.1
    simpa only [stateB.rsp,frameBase,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · exact init.writes.2.2.2.2.2.2.2.1
  · exact init.writes.2.2.2.2.2.2.2.2.1
  · exact init.writes.2.2.2.2.2.2.2.2.2

end P256.Proofs.Verifying.Core.Digest
