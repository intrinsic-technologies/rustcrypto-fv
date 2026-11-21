import P256.Proofs.Verifying.Core.Scalars.FirstSetup.Block

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars.FirstSetup

open P256.Spec.Program P256.Spec.Program.Routines Prelude Block
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dca0) : Block.Pre t := by
  refine ⟨rip,?_,?_,?_⟩
  · intro offset ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    exact stack_readable (frameOffset := 1176) hp.toCalleePre state (by decide) (by omega)
  · intro offset ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact local_writable8 hp state (by decide) (by decide)
  · intro offset ho codeOffset len hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    have addr : (0x10dca0 : BitVec 64)+BitVec.ofNat 64 codeOffset =
        Extracted.textAddress+BitVec.ofNat 64 (0xdca0+codeOffset) := by
      rw [BitVec.ofNat_add,← BitVec.add_assoc]
      rfl
    rw [addr]
    exact stack_code (frameOffset := 1176) hp.toCalleePre state (by decide) (by omega) (by omega)

theorem writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) :
    WritesWithin (effect t).components #v[workRegion s 9992] := by
  intro c hc a covered
  simp only [effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals exact ⟨_,by simp,local_work_contains hp state (by decide) covered⟩

theorem prefix_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) :
    WritesWithin (effect t).components (prefixRegions s) := by
  intro c hc a covered
  simp only [effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals exact prefix_local_contains hp state (by decide) covered

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dca0) :
    ∃ n u, Advances boundary n t u ∧ Frame s u ∧ (effect t).Holds t u ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  obtain ⟨n,u,run,ready,_,he⟩ := block boundary
    (fun i hi => by
      have addr : (0x10dca0 : BitVec 64)+BitVec.ofNat 64 i =
          Extracted.textAddress+BitVec.ofNat 64 (0xdca0+i) := by
        rw [BitVec.ofNat_add,← BitVec.add_assoc]
        rfl
      rw [addr]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xdca0 bytes
      (by decide) extracted_bytes) (pre hp state rip)
  have st := state.after_effect hp.toCalleePre (by decide) ready he.agrees (by
    intro c hc a ha
    obtain ⟨region,hr,hin⟩ := writes hp state c hc a ha
    exact ⟨region,by simpa using Or.inr hr,hin⟩) (by simp [effect,Effect.components])
  exact ⟨n,u,run,st,he,he.agrees.memoryWriteFrame (prefix_writes hp state)⟩

end P256.Proofs.Verifying.Core.Scalars.FirstSetup
