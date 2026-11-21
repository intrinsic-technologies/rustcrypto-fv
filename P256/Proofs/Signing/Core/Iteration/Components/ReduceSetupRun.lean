import P256.Proofs.Signing.Core.Iteration.Components.ReduceSetup
import P256.Proofs.Signing.Core.Iteration.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.ReduceSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d21a) : Pre t := by
  have sp : rspOf t = frameBase s := frame.rsp
  refine ⟨rip,?_,?_,?_⟩
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rw [sp]
    exact local_readable hp frame (by omega)
  · intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rw [sp]
    exact local_writable8 hp frame (by omega) (by omega)
  · intro off ho i len hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rw [sp]
    have addr : (0x10d21a : BitVec 64)+BitVec.ofNat 64 i =
        Extracted.textAddress+BitVec.ofNat 64 (0xd21a+i) := by
      rw [BitVec.ofNat_add,← BitVec.add_assoc]
      rfl
    rw [addr]
    exact local_code_apart hp frame (by omega) (by omega)

theorem writes [Bindings] {s t : RamState} (frame : Frame s t) :
    WordWrites (frameBase s) [528, 536, 544, 552] (effect t).components := by
  intro c hc address ha
  simp only [effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i,hi,rfl⟩ := ha
  · exact ⟨552,by simp,i,hi,congrArg (fun b => b+552+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨544,by simp,i,hi,congrArg (fun b => b+544+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨536,by simp,i,hi,congrArg (fun b => b+536+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨528,by simp,i,hi,congrArg (fun b => b+528+BitVec.ofNat 64 i) frame.rsp⟩

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d21a) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ (effect t).Holds t u := by
  obtain ⟨n,u,run,ready,_,effect⟩ := block boundary
    (fun i hi => by
      have addr : (0x10d21a : BitVec 64)+BitVec.ofNat 64 i =
          Extracted.textAddress+BitVec.ofNat 64 (0xd21a+i) := by
        rw [BitVec.ofNat_add,← BitVec.add_assoc]
        rfl
      rw [addr]
      exact boundary_ne_program hp.outerBoundary (inProgram_of_textOffset _ (by omega)))
    t (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd21a bytes
      (by decide) (by decide +kernel)) (pre hp frame rip)
  refine ⟨n,u,run,after_effect hp frame ready effect.agrees (writes frame) ?_
    (by simp [ReduceSetup.effect,Effect.components]) (by simp [ReduceSetup.effect,Effect.components])
    (by simp [ReduceSetup.effect,Effect.components]) (by simp [ReduceSetup.effect,Effect.components]),effect⟩
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  omega

theorem byte [Bindings] {s t u : RamState} (frame : Frame s t)
    (result : (effect t).Holds t u) {offset : Nat} (bound : offset < 2280)
    (apart : offset < 528 ∨ 560 ≤ offset) :
    u.external[frameBase s+BitVec.ofNat 64 offset]? =
      t.external[frameBase s+BitVec.ofNat 64 offset]? := by
  apply word_writes_byte (writes frame) result.agrees (by omega)
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  omega

theorem copied [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x : Nat}
    (hp : SignPre s boundary) (frame : Frame s t) (out : Frame s u)
    (result : (effect t).Holds t u) (input : Nat256At t (frameBase s+1328) x) :
    Nat256At u (frameBase s+528) x := by
  apply Verifying.Core.Scalars.nat256_word_copy input
    (local_readable hp out (offset := 528) (len := 32) (by decide))
  have sp : rspOf t = frameBase s := frame.rsp
  rcases result.writes with ⟨_,_,_,_,_,h3,h2,h1,h0⟩
  intro j hj
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl|rfl
  all_goals simp only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,
    BitVec.reduceAdd,BitVec.add_zero]
  · simp only [Write.AllHold, memLoad_external, sp] at h0
    exact h0
  · simp only [memLoad_external, sp] at h1
    exact h1
  · simp only [memLoad_external, sp] at h2
    exact h2
  · simp only [memLoad_external, sp] at h3
    exact h3

end P256.Proofs.Signing.Core.Iteration.Components.ReduceSetup
