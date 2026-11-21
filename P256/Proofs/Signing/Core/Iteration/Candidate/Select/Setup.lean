import P256.Proofs.Signing.Core.Iteration.Candidate.Select.Block
import P256.Proofs.Signing.Core.Iteration.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Select

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Signing.Core.Iteration
open Block

theorem pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cb11) : Pre t := by
  have sp : rspOf t = frameBase s := frame.rsp
  refine ⟨rip, ?_, ?_, ?_⟩
  · rw [sp]
    exact local_readable hp frame (by decide)
  · intro offset ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [sp]
    exact local_writable8 hp frame (by omega) (by omega)
  · intro offset ho codeOffset len hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [sp]
    have code : (0x10cb11 : BitVec 64) + BitVec.ofNat 64 codeOffset =
        Extracted.textAddress + BitVec.ofNat 64 (0xcb11 + codeOffset) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    rw [code]
    exact local_code_apart hp frame (by omega) (by omega)

theorem writes [Bindings] {s t : RamState} (frame : Frame s t) :
    WordWrites (frameBase s) [176, 184, 192, 200] (effect t).components := by
  intro c hc address ha
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  · exact ⟨200, by simp, i, hi, congrArg (fun b => b + 200 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨192, by simp, i, hi, congrArg (fun b => b + 192 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨184, by simp, i, hi, congrArg (fun b => b + 184 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨176, by simp, i, hi, congrArg (fun b => b + 176 + BitVec.ofNat 64 i) frame.rsp⟩

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cb11) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (effect t).Holds t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block boundary
    (fun i hi => by
      have addr : (0x10cb11 : BitVec 64) + BitVec.ofNat 64 i =
          Extracted.textAddress + BitVec.ofNat 64 (0xcb11 + i) := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      rw [addr]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xcb11 Block.bytes
      (by decide +kernel) (by decide +kernel)) (pre hp frame rip)
  refine ⟨fuel, u, run, after_effect hp frame ready effect.agrees (writes frame) ?_
    (by simp [Block.effect, Effect.components]) (by simp [Block.effect, Effect.components])
    (by simp [Block.effect, Effect.components]) (by simp [Block.effect, Effect.components]), effect⟩
  intro off ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  omega

end P256.Proofs.Signing.Core.Iteration.Candidate.Select
