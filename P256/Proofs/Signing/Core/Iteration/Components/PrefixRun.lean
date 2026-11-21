import P256.Proofs.Signing.Core.Iteration.Components.Prefix
import P256.Proofs.Signing.Core.Iteration.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem writable_narrow {s : RamState} {a : BitVec 64} {len : Nat}
    (h : MemWritable s a 8) (bound : len ≤ 8) : MemWritable s a len := by
  refine ⟨by have := h.low; omega,
    fun i hi => h.mem i (by omega), ?_⟩
  exact h.tables.sub (by omega) (by omega)

theorem pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d19f) : Pre t := by
  have sp : rspOf t = frameBase s := frame.rsp
  refine ⟨rip, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]
    exact writable_narrow (local_writable8 hp frame (offset := 528) (by decide) (by decide)) (by decide)
  · rw [sp]
    exact Common.Instructions.CrossPageStore.Writable.of_memWritable
      (writable_narrow (local_writable8 hp frame (offset := 8) (by decide) (by decide)) (by decide))
  · intro offset ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rw [sp]
    rcases ho with rfl|rfl|rfl|rfl <;> exact local_writable8 hp frame (by decide) (by decide)
  · intro off len hl
    rw [sp]
    exact local_code_apart hp frame (offset := 528) (len := 1) (by decide) hl
  · intro off len hl
    rw [sp]
    exact local_code_apart hp frame (offset := 8) (len := 4) (by decide) hl
  · intro offset ho off len hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rw [sp]
    rcases ho with rfl|rfl|rfl|rfl <;> exact local_code_apart hp frame (by decide) hl

theorem writes [Bindings] {s t : RamState} (frame : Frame s t) :
    WordWrites (frameBase s) [528,8,1352,1344,1336,1328] (effect t).components := by
  intro c hc address ha
  simp only [effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i,hi,rfl⟩ := ha
  · exact ⟨528,by simp,i,by omega,congrArg (fun b => b+528+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨8,by simp,i,by omega,congrArg (fun b => b+8+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨1352,by simp,i,hi,congrArg (fun b => b+1352+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨1344,by simp,i,hi,congrArg (fun b => b+1344+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨1336,by simp,i,hi,congrArg (fun b => b+1336+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨1328,by simp,i,hi,congrArg (fun b => b+1328+BitVec.ofNat 64 i) frame.rsp⟩

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d19f) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (effect t).Holds t u := by
  obtain ⟨n,u,run,ready,_,effect⟩ := block boundary hp.outerBoundary t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd19f bytes
      (by decide) (by decide +kernel)) (pre hp frame rip)
  refine ⟨n,u,run,after_effect hp frame ready effect.agrees (writes frame) ?_
    (by simp [Prefix.effect,Effect.components]) (by simp [Prefix.effect,Effect.components])
    (by simp [Prefix.effect,Effect.components]) (by simp [Prefix.effect,Effect.components]),effect⟩
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  omega

theorem byte [Bindings] {s t u : RamState} (frame : Frame s t)
    (result : (effect t).Holds t u) {offset : Nat} (bound : offset < 2280)
    (low : 16 ≤ offset) (apart : offset < 528 ∨ 536 ≤ offset)
    (high : offset < 1328 ∨ 1360 ≤ offset) :
    u.external[frameBase s+BitVec.ofNat 64 offset]? =
      t.external[frameBase s+BitVec.ofNat 64 offset]? := by
  apply word_writes_byte (writes frame) result.agrees (by omega)
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  omega

end P256.Proofs.Signing.Core.Iteration.Components.Prefix
