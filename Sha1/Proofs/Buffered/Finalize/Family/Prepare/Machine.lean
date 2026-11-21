import Sha1.Proofs.Buffered.Finalize.Steps
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Sha1.Proofs.Buffered.Finalize.Family.PrepareMachine

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

private def entryBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x20, 0x48, 0x8d, 0xb4, 0x24, 0xd8, 0, 0, 0,
    0xb9, 0x0c, 0, 0, 0]

def entryEffect (s : RamState) : Effect :=
  { rip := 0x101ddd
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 32⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 216⟩,
      ⟨(.reg 1 : Operand 64), 12⟩] }

private theorem entryExecution [Bindings] (b : ReturnBoundary) (outside : ¬ InProgram b.rip) :
    AdvancesBlock b (fun s ↦ s.RIP = 0x101dcb) (codeRange 0x101dcb entryBytes) entryEffect := by
  unfold entryBytes
  md5_run_begin lea_r64_effect_step 0x101dcb 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 32)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return outside 0x1dd0 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x101dd0 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d32 216)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101dcb) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return outside 0x1dd8 (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x101dd8 0xb9 (by decide) 12
  case sub => exact codeRange_mem_of_drop (p := 0x101dcb) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return outside 0x1ddd (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [entryEffect]
  · x86_norm [entryEffect, stackPtr]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [entryEffect]
  · x86_norm [entryEffect]

theorem entry [Bindings] {b : ReturnBoundary} {m : ByteArray} {s : RamState}
    (h : Pre .updateFinalizeCopy b m s) :
    ∃ fuel t, Advances b fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (entryEffect s).Holds s t := by
  have hc : CodeIn (codeRange 0x101dcb entryBytes) s :=
    program_text_slice h.code 0x1dcb 18 (by decide +kernel)
  obtain ⟨fuel, t, ha, hr, _, he⟩ := entryExecution b h.boundaryOutside s h.ready hc h.rip
  refine ⟨fuel, t, ha, hr, he.codeIn ?_ h.code, he⟩
  apply Effect.Avoids.of_noMem
  simp [entryEffect, Effect.components, Component.Covers]

private def bytesA : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0x74, 0x24, 0x5f, 0x4c, 0x8b, 0x7c, 0x24, 0x60,
    0x48, 0x8d, 0x8c, 0x24, 0x20, 0x01, 0, 0, 0x8b, 0x41, 0x10, 0x89, 0x44, 0x24, 0x18]

private def bytesB : List UInt8 :=
  [0x48, 0x8b, 0x01, 0x48, 0x8b, 0x49, 0x08, 0x48, 0x89, 0x4c, 0x24, 0x10,
    0x48, 0x89, 0x44, 0x24, 0x08]

def effectA (s : RamState) : Effect :=
  { rip := 0x101dfa
    writes := [
      ⟨(.reg 14 : Operand 64), ((Operand.mem (stackPtr s + 95) : Operand 8).read s).setWidth 64⟩,
      ⟨(.reg 15 : Operand 64), (Operand.mem (stackPtr s + 96) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), stackPtr s + 288⟩,
      ⟨(.reg 0 : Operand 64), ((Operand.mem (stackPtr s + 304) : Operand 32).read s).setWidth 64⟩,
      ⟨(.mem (stackPtr s + 24) : Operand 32), (Operand.mem (stackPtr s + 304) : Operand 32).read s⟩] }

def effectB (s : RamState) : Effect :=
  { rip := 0x101e0b
    writes := [
      ⟨(.reg 0 : Operand 64), (Operand.mem (stackPtr s + 288) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (Operand.mem (stackPtr s + 296) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 16) : Operand 64), (Operand.mem (stackPtr s + 296) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 8) : Operand 64), (Operand.mem (stackPtr s + 288) : Operand 64).read s⟩] }

private structure StatePointer (s : RamState) : Prop extends Steps.PartPre .updateFinalizeCopy 0x101dfa s where
  pointer : (Operand.reg 1 : Operand 64).read s = stackPtr s + 288

set_option maxHeartbeats 1000000 in
private theorem executionA [Bindings] (b : ReturnBoundary) (outside : ¬ InProgram b.rip) :
    AdvancesBlock b (Steps.PartPre .updateFinalizeCopy 0x101de0) (codeRange 0x101de0 bytesA)
      effectA := by
  unfold bytesA
  md5_run_begin movzx_r_m8_rex_effect_step 0x101de0 0x44 (by unfold RexPrefix; decide)
    32 (.inr rfl) (fun _ ↦ rfl) 6 (.sib 4 none 0 (.d8 95))
    (by decide) (by decide) (by decide)
  case pre => intro s h; exact ⟨h.rip, (h.toStorage.stackWritable 95 1 (by decide)).readable⟩
  case boundary => intro _ _; exact text_address_ne_return outside 0x1de6 (by decide +kernel)
  md5_run_then mov_r64_m64_effect_step 0x101de6 0x4c (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101de0) 6 (by decide +kernel)
  case mid =>
    intro s t h he ho
    refine ⟨LoadPre.of_holds he (ho true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      exact (h.toStorage.stackWritable 96 8 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return outside 0x1deb (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x101deb 0x48 (by unfold RexWPrefix; decide)
    1 (.sib 4 none 0 (.d32 288)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101de0) 11 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return outside 0x1df3 (by decide +kernel)
  md5_run_then mov_r32_m32_low_effect_step 0x101df3 0 (.base 1 (.d8 16))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101de0) 19 (by decide +kernel)
  case mid =>
    intro s t h he ho
    refine ⟨LoadPre.of_holds he (ho true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm [stackPtr]
      exact (h.toStorage.stackWritable 304 4 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return outside 0x1df6 (by decide +kernel)
  md5_run_then Common.Instructions.MovStore.mov_m32_r32_low_effect_step 0x101df6
    0 (.sib 4 none 0 (.d8 24)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101de0) 22 (by decide +kernel)
  case mid =>
    intro s t h he ho
    have hsp : stackPtr t = stackPtr s := he.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨storePre_of_holds he (ho true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 24 4 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 24) (len := 4) (codeOffset := 0x1df6)
        (codeLen := 4) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (by rfl)
      x86_norm
      change RangeApart (stackPtr t + 24) 4 0x101de0 26
      rw [hsp]
      exact h.toStorage.stackApart (offset := 24) (len := 4) (codeOffset := 0x1de0)
        (codeLen := 26) (by decide) (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return outside 0x1dfa (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [effectA]
  · x86_norm [effectA, stackPtr]
    refine ⟨.inl rfl, .inl rfl, .inl rfl, .inl rfl, .inr (.inr (.inr (.inr ⟨rfl, ?_⟩)))⟩
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    rfl
  · intro i; cases i <;> x86_norm [effectA]
  · x86_norm [effectA, stackPtr]
    rfl

set_option maxHeartbeats 1000000 in
private theorem executionB [Bindings] (b : ReturnBoundary) (outside : ¬ InProgram b.rip) :
    AdvancesBlock b StatePointer (codeRange 0x101dfa bytesB) effectB := by
  unfold bytesB
  md5_run_begin mov_r64_m64_effect_step 0x101dfa 0x48 (by unfold RexWPrefix; decide)
    0 (.base 1 .none) (by decide) (by decide) (by decide)
  case pre =>
    intro s h
    refine ⟨h.toPartPre.rip, ?_⟩
    x86_norm
    simp only [BitVec.add_zero]
    change MemReadable s ((Operand.reg 1 : Operand 64).read s) 8
    rw [h.pointer]
    exact (h.toPartPre.toStorage.stackWritable 288 8 (by decide)).readable
  case boundary => intro _ _; exact text_address_ne_return outside 0x1dfd (by decide +kernel)
  md5_run_then mov_r64_m64_effect_step 0x101dfd 0x48 (by unfold RexWPrefix; decide)
    1 (.base 1 (.d8 8)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101dfa) 3 (by decide +kernel)
  case mid =>
    intro s t h he ho
    refine ⟨LoadPre.of_holds he (ho true) (by x86_norm) (by x86_addr_obs) ?_, ?_⟩
    · x86_norm
      change MemReadable s ((Operand.reg 1 : Operand 64).read s + 8) 8
      rw [h.pointer, BitVec.add_assoc]
      exact (h.toPartPre.toStorage.stackWritable 296 8 (by decide)).readable
    · x86_avoid
  case boundary => intro _ _; exact text_address_ne_return outside 0x1e01 (by decide +kernel)
  storage_copy_store .updateFinalizeCopy, 0x101e01, 0x101dfa, 17, 7, 0x48, 1, 16,
    (.sib 4 none 0 (.d8 16)), 5
  storage_copy_store .updateFinalizeCopy, 0x101e06, 0x101dfa, 17, 12, 0x48, 0, 8,
    (.sib 4 none 0 (.d8 8)), 5
  apply AdvancesBlock.block_end
  intro s t h he
  have h0 : (Operand.reg 1 : Operand 64).read s + 0#64 = stackPtr s + 288 := by
    rw [h.pointer, BitVec.add_zero]
  have h8 : (Operand.reg 1 : Operand 64).read s + 8#64 = stackPtr s + 296 := by
    rw [h.pointer, BitVec.add_assoc]
    rfl
  apply he.weaken
  · x86_norm [effectB]
  · x86_norm [effectB, stackPtr]
    refine ⟨?_, ?_, .inl ⟨rfl, ?_⟩, .inr ⟨rfl, ?_⟩⟩
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h0.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h8.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h8.symm
    · exact congrArg (fun a ↦ (Operand.mem a : Operand 64).read s) h0.symm
  · intro i; cases i <;> x86_norm [effectB]
  · x86_norm [effectB, stackPtr]
    exact ⟨.inl rfl, .inr rfl⟩

theorem effectA_rsp {s t : RamState} (h : (effectA s).Holds s t) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [effectA, Effect.components])

theorem effectB_rsp {s t : RamState} (h : (effectB s).Holds s t) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp [effectB, Effect.components])

private theorem effectA_avoids {s : RamState} (h : Storage .updateFinalizeCopy s) :
    (effectA s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effectA, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  exact h.stackAvoids x.1 (h.stackCover (offset := 24) (len := 4) (by decide) ha)
    (.inl ⟨x.2, hx⟩)

private theorem effectB_avoids {s : RamState} (h : Storage .updateFinalizeCopy s) :
    (effectB s).Avoids Extracted.programImage := by
  intro x hx c hc ha
  simp only [effectB, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact h.stackAvoids x.1 (h.stackCover (offset := 16) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)
  · exact h.stackAvoids x.1 (h.stackCover (offset := 8) (len := 8) (by decide) ha)
      (.inl ⟨x.2, hx⟩)

theorem normalize [Bindings] {b : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (outside : ¬ InProgram b.rip)
    (hs : Storage .updateFinalizeCopy s) (rip : s.RIP = 0x101de0) :
    ∃ fuel u t, Advances b fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (effectA s).Holds s u ∧ (effectB u).Holds u t := by
  have hca : CodeIn (codeRange 0x101de0 bytesA) s :=
    program_text_slice hc 0x1de0 26 (by decide +kernel)
  obtain ⟨n, u, ha, hra, _, he⟩ := executionA b outside s hr hca ⟨hs, rip⟩
  have hua := he.codeIn (effectA_avoids hs) hc
  have hsp := effectA_rsp he
  have hu : StatePointer u :=
    ⟨⟨hs.of_agrees he.agrees hsp, he.rip⟩, hsp.symm ▸ he.writes.2.2.1⟩
  have hcb : CodeIn (codeRange 0x101dfa bytesB) u :=
    program_text_slice hua 0x1dfa 17 (by decide +kernel)
  obtain ⟨m, t, hb, hrb, _, he'⟩ := executionB b outside u hra hcb hu
  exact ⟨n + m, u, t, ha.trans hb, hrb, he'.codeIn (effectB_avoids hu.toPartPre.toStorage) hua,
    he, he'⟩

end Sha1.Proofs.Buffered.Finalize.Family.PrepareMachine
