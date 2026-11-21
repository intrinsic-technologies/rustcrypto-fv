import Sha2.Proofs.Digest.Absorb.BulkSetup
import Sha2.Proofs.Digest.Absorb.TailLength
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Common.Machine.FrameMemory

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512

 theorem bulk_setup [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs .digest) (input : Preserved v initial s .digest)
    (rip : s.RIP = v.pc 0xeb .digest) :
    ∃ t, Preserved v initial t .digest ∧
      (BulkSetup.effect (v.pc 0xeb .digest) s).Holds s t := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside : BlockInProgram (v.pc 0xeb .digest) BulkSetup.bytes.length := by
    intro i hi
    rw [Variant.pc_add _ _ _ .digest]
    apply Variant.pc_inProgram (form := .digest)
    change i ≤ 55 at hi
    omega
  have rsp : rspOf s = stackPtr initial - 600 := input.rsp
  have avoid := (ctx.separation.2 (Stack.region initial 1152)
    (by
      change Stack.region initial 1152 ∈
        [v.outputRegion initial .digest, Stack.region initial 1152]
      simp)).2
  have writable (offset : Nat) (bound : offset + 8 ≤ 600) :
      MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8 := by
    rw [rsp]
    exact stack_frame_writable ctx.stack (by change 600 ≤ 1152; decide)
      (fun a ha h => avoid a ha (.inr h)) input.allocated bound (by decide)
  have apart (offset : Nat) (bound : offset + 8 ≤ 600) :
      RangeApart (rspOf s + BitVec.ofNat 64 offset) 8 (v.pc 0xeb .digest) BulkSetup.bytes.length := by
    rw [rsp]
    exact stack_frame_codeApart ctx.stack (by change 600 ≤ 1152; decide)
      (fun a ha h => avoid a ha (.inl h)) bound (fun i hi => inside i (by omega))
  have pre : BulkSetup.Pre (v.pc 0xeb .digest) s :=
    ⟨rip, .of_memWritable (writable 400 (by decide)), .of_memWritable (writable 408 (by decide)),
      apart 400 (by decide), apart 408 (by decide)⟩
  obtain ⟨fuel,t,run,ready,_,effect⟩ := BulkSetup.run (v.pc 0xeb .digest)
    (returnBoundary initial) outside inside s (supportedMachine_readyToStep input.machine)
    (BulkSetup.code v input.loaded) pre
  have localWrites : Wrapper512.Absorb.LocalWrites initial
      (BulkSetup.effect (v.pc 0xeb .digest) s).components .digest := by
    intro c hc a ha
    simp only [BulkSetup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv] at hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals simp only [rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd] at ha
    · apply Wrapper512.Absorb.local_memory (form := .digest) (offset := 200) (len := 8)
        (by decide) (by decide) (Or.inr (by decide)) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.reduceNeg] using ha
    · apply Wrapper512.Absorb.local_memory (form := .digest) (offset := 192) (len := 8)
        (by decide) (by decide) (Or.inr (by decide)) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.reduceNeg] using ha
  exact ⟨t, Wrapper512.Absorb.preserved_of_agrees ctx input run ready effect.agrees localWrites
    (by simp [BulkSetup.effect, Effect.components, Write.component, Operand.component])
    (by simp [BulkSetup.effect, Effect.components, Write.component, Operand.component])
    (by simp [BulkSetup.effect, Effect.components, Write.component, Operand.component]), effect⟩

theorem tail_length [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs .digest) (input : Preserved v initial s .digest)
    (short : Bool) (rip : s.RIP = v.pc (if short then 0xe1 else 0x127) .digest) :
    ∃ t, Preserved v initial t .digest ∧
      (TailLength.effect (v.pc (if short then 0xe1 else 0x127) .digest) short s).Holds s t := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside : BlockInProgram (v.pc (if short then 0xe1 else 0x127) .digest)
      (TailLength.bytes short).length := by
    intro i hi
    rw [Variant.pc_add _ _ _ .digest]
    apply Variant.pc_inProgram (form := .digest)
    cases short <;> simp only [TailLength.bytes, List.length_append, List.length_cons,
      List.length_nil, Bool.false_eq_true, ite_false, ite_true] at hi ⊢ <;> omega
  have target : InProgram (v.pc (if short then 0xe1 else 0x127) .digest + 98) := by
    change InProgram (v.pc (if short then 0xe1 else 0x127) .digest + BitVec.ofNat 64 98)
    rw [Variant.pc_add _ _ 98 .digest]
    exact Variant.pc_inProgram v (by cases short <;> decide) .digest
  have rsp : rspOf s = stackPtr initial - 600 := input.rsp
  have avoid := (ctx.separation.2 (Stack.region initial 1152)
    (by
      change Stack.region initial 1152 ∈
        [v.outputRegion initial .digest, Stack.region initial 1152]
      simp)).2
  have pre : TailLength.Pre (v.pc (if short then 0xe1 else 0x127) .digest) short s := by
    refine ⟨rip, ?_, ?_⟩
    · rw [rsp]
      exact stack_frame_writable ctx.stack (by change 600 ≤ 1152; decide)
        (fun a ha h => avoid a ha (.inr h)) input.allocated (by decide) (by decide)
    · rw [rsp]
      exact stack_frame_codeApart ctx.stack (by change 600 ≤ 1152; decide)
        (fun a ha h => avoid a ha (.inl h)) (by decide) (fun i hi => inside i (by omega))
  obtain ⟨fuel,t,run,ready,_,effect⟩ := TailLength.run
    (v.pc (if short then 0xe1 else 0x127) .digest) short (returnBoundary initial)
    outside inside target s (supportedMachine_readyToStep input.machine)
    (TailLength.code v short input.loaded) pre
  have localWrites : Wrapper512.Absorb.LocalWrites initial
      (TailLength.effect (v.pc (if short then 0xe1 else 0x127) .digest) short s).components .digest := by
    intro c hc a ha
    simp only [TailLength.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, Nat.reduceDiv, List.cons_append, List.nil_append] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp only [rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] at ha
      apply Wrapper512.Absorb.local_memory (form := .digest) (offset := 265) (len := 1)
        (by decide) (by decide) (Or.inr (by decide)) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.reduceNeg] using ha
    · exact ha.elim
  exact ⟨t, Wrapper512.Absorb.preserved_of_agrees ctx input run ready effect.agrees localWrites
    (by simp [TailLength.effect, Effect.components, Write.component, Operand.component])
    (by simp [TailLength.effect, Effect.components, Write.component, Operand.component])
    (by simp [TailLength.effect, Effect.components, Write.component, Operand.component]), effect⟩

end Sha2.Proofs.Digest.Absorb
