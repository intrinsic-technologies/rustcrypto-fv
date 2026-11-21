import P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Setup.Block
import P256.Proofs.Signing.Core.Iteration.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Setup

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Signing.Core.Iteration
open Block

theorem pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cb5f) : Pre t := by
  have sp : rspOf t = frameBase s := frame.rsp
  refine ⟨rip, ?_, ?_⟩
  · intro offset ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [sp]
    exact local_writable8 hp frame (by omega) (by omega)
  · intro offset ho codeOffset len hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [sp]
    have code : (0x10cb5f : BitVec 64) + BitVec.ofNat 64 codeOffset =
        Extracted.textAddress + BitVec.ofNat 64 (0xcb5f + codeOffset) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    rw [code]
    exact local_code_apart hp frame (by omega) (by omega)

theorem writes [Bindings] {s t : RamState} (frame : Frame s t) :
    WordWrites (frameBase s) [1328, 1336, 1344, 1352] (effect t).components := by
  intro c hc address ha
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  · exact ⟨1352, by simp, i, hi, congrArg (fun b => b + 1352 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨1344, by simp, i, hi, congrArg (fun b => b + 1344 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨1336, by simp, i, hi, congrArg (fun b => b + 1336 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨1328, by simp, i, hi, congrArg (fun b => b + 1328 + BitVec.ofNat 64 i) frame.rsp⟩

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cb5f) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (effect t).Holds t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block boundary
    (fun i hi => by
      have addr : (0x10cb5f : BitVec 64) + BitVec.ofNat 64 i =
          Extracted.textAddress + BitVec.ofNat 64 (0xcb5f + i) := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      rw [addr]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xcb5f Block.bytes
      (by decide +kernel) (by decide +kernel)) (pre hp frame rip)
  refine ⟨fuel, u, run, after_effect hp frame ready effect.agrees (writes frame) ?_
    (by simp [Block.effect, Effect.components]) (by simp [Block.effect, Effect.components])
    (by simp [Block.effect, Effect.components]) (by simp [Block.effect, Effect.components]), effect⟩
  intro off ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  omega

theorem zero [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (out : Frame s u)
    (effect : (Block.effect t).Holds t u) :
    P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At u (frameBase s + 1328) 0 := by
  apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs (by decide)
    (local_readable hp out (offset := 1328) (len := 32) (by decide)).mem
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  have sp : rspOf t = frameBase s := frame.rsp
  rcases cases with rfl | rfl | rfl | rfl
  · simpa only [Write.AllHold, memLoad_external, sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul, Nat.zero_div] using effect.writes.2.2.2.1
  · simpa only [Write.AllHold, memLoad_external, sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul, Nat.zero_div] using effect.writes.2.2.1
  · simpa only [Write.AllHold, memLoad_external, sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul, Nat.zero_div] using effect.writes.2.1
  · simpa only [Write.AllHold, memLoad_external, sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul, Nat.zero_div] using effect.writes.1

end P256.Proofs.Signing.Core.Iteration.Candidate.Finish.Setup
