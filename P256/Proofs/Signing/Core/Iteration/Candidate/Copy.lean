import P256.Proofs.Signing.Core.Iteration.Candidate.Copy.Block
import P256.Proofs.Signing.Core.Iteration.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Copy

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Signing.Core.Iteration
open Block

theorem pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cad9) : Pre t := by
  have sp : rspOf t = frameBase s := frame.rsp
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro offset ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [sp]
    exact local_readable hp frame (by omega)
  · intro offset ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [sp]
    exact local_writable8 hp frame (by omega) (by omega)
  · intro offset ho codeOffset len hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [sp]
    have code : (0x10cad9 : BitVec 64) + BitVec.ofNat 64 codeOffset =
        Extracted.textAddress + BitVec.ofNat 64 (0xcad9 + codeOffset) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    rw [code]
    exact local_code_apart hp frame (by omega) (by omega)

theorem writes [Bindings] {s t : RamState} (frame : Frame s t) :
    WordWrites (frameBase s) [104, 112, 120, 128] (effect t).components := by
  intro c hc address ha
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i, hi, rfl⟩ := ha
  · exact ⟨104, by simp, i, hi, congrArg (fun b => b + 104 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨112, by simp, i, hi, congrArg (fun b => b + 112 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨120, by simp, i, hi, congrArg (fun b => b + 120 + BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨128, by simp, i, hi, congrArg (fun b => b + 128 + BitVec.ofNat 64 i) frame.rsp⟩

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cad9) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (effect t).Holds t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block boundary
    (fun i hi => by
      have addr : (0x10cad9 : BitVec 64) + BitVec.ofNat 64 i =
          Extracted.textAddress + BitVec.ofNat 64 (0xcad9 + i) := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      rw [addr]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xcad9 Block.bytes
      (by decide +kernel) (by decide +kernel)) (pre hp frame rip)
  refine ⟨fuel, u, run, after_effect hp frame ready effect.agrees (writes frame) ?_
    (by simp [Block.effect, Effect.components]) (by simp [Block.effect, Effect.components])
    (by simp [Block.effect, Effect.components]) (by simp [Block.effect, Effect.components]), effect⟩
  intro off ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  omega

theorem copied [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (out : Frame s u)
    (effect : (Block.effect t).Holds t u) :
    ∀ i < 32, u.external[frameBase s + 104 + BitVec.ofNat 64 i]? =
      t.external[frameBase s + 40 + BitVec.ofNat 64 i]? := by
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_, _, _, _, h0, h1, h2, h3⟩
  have sp : rspOf t = frameBase s := frame.rsp
  have words (j : Nat) (hj : j < 4) :
      memLoad u.external (frameBase s + 104 + BitVec.ofNat 64 (8*j)) 64 =
        memLoad t.external (frameBase s + 40 + BitVec.ofNat 64 (8*j)) 64 := by
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Write.AllHold, memLoad_external, sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h0
    · simpa only [Write.AllHold, memLoad_external, sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h1
    · simpa only [Write.AllHold, memLoad_external, sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h2
    · simpa only [Write.AllHold, memLoad_external, sp, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, BitVec.reduceAdd, Nat.reduceMul] using h3
  have readable := local_readable hp frame (offset := 40) (len := 32) (by decide)
  have allocated := local_readable hp out (offset := 104) (len := 32) (by decide)
  intro i hi
  have src := Bytes.of_memLoad (n := 64)
    (a := frameBase s + 40 + BitVec.ofNat 64 (8*(i/8))) (m := t.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem (8*(i/8)+j) (by omega))
  have dst := Bytes.of_memLoad (n := 64)
    (a := frameBase s + 104 + BitVec.ofNat 64 (8*(i/8))) (m := u.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated.mem (8*(i/8)+j) (by omega))
  rw [words (i/8) (by omega)] at dst
  have eq := (dst (i%8) (by omega)).trans (src (i%8) (by omega)).symm
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8=i by omega] using eq

end P256.Proofs.Signing.Core.Iteration.Candidate.Copy
