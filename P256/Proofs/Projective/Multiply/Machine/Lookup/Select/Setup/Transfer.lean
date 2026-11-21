import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Prologue
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Machine.Suffix
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Machine.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (CalleePre)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem scratch_offset {s : RamState} {i : Nat} (hi : i ∈ [0, 8, 16, 24]) :
    scratch s + BitVec.ofNat 64 i = stackPtr s - BitVec.ofNat 64 (40 - i) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc] <;> rfl

theorem setup_limb_offset {i : BitVec 64}
    (hi : i ∈ ([0, 8, 16, 24] : List (BitVec 64))) :
    ∃ n ∈ ([0, 8, 16, 24] : List Nat), i = BitVec.ofNat 64 n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨0, by simp, rfl⟩
  · exact ⟨8, by simp, rfl⟩
  · exact ⟨16, by simp, rfl⟩
  · exact ⟨24, by simp, rfl⟩

theorem setup_limb_bound {i : Nat} (hi : i ∈ [0, 8, 16, 24]) : i ≤ 24 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> decide

theorem setup_suffix_pre [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x114380 32 32 128)
    (effect : (prepareEffect s).Holds s u) : SetupSuffixPre u := by
  have rsp : (Operand.reg 4 : Operand 64).read u = scratch s := effect.writes.1
  have rsi : (Operand.reg 6 : Operand 64).read u = s.regValue .rsi :=
    effect.agrees.read (n := 64) (r := 6) (by simp [prepareEffect, Effect.components])
  refine ⟨effect.rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn, rfl⟩ := setup_limb_offset hi
    rw [rsi]
    exact (setup_input_readable pre (by have := setup_limb_bound hn; omega)).of_holds effect
  · intro i hi
    obtain ⟨n, hn, rfl⟩ := setup_limb_offset hi
    rw [rsp, scratch_offset hn]
    apply MemWritable.of_holds effect
    apply P256.Proofs.Program.stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  · intro i hi offset len hcode
    obtain ⟨n, hn, rfl⟩ := setup_limb_offset hi
    rw [rsp, scratch_offset hn]
    exact setup_stack_codeApart pre (by omega) (by omega) hcode
  · intro i hi j hj
    obtain ⟨n, hn, rfl⟩ := setup_limb_offset hi
    obtain ⟨m, hm, rfl⟩ := setup_limb_offset hj
    rw [rsp, scratch_offset hn, rsi]
    exact setup_stack_sourceApart pre (by omega) (by omega)
      (by have := setup_limb_bound hm; omega)

theorem prepare_source_word [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x114380 32 32 128)
    (effect : (prepareEffect s).Holds s u) {offset : Nat} (hoff : offset + 8 ≤ 32) :
    (Operand.mem (s.regValue .rsi + BitVec.ofNat 64 offset) : Operand 64).read u =
      (Operand.mem (s.regValue .rsi + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  have hb : u.external[s.regValue .rsi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    apply effect.agrees.byte
    intro c hc ha
    simp only [prepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    obtain ⟨j, hj, heq⟩ := ha
    exact setup_stack_sourceApart pre (offset := 8) (by decide) (by decide) hoff
      j hj i hi heq.symm
  simp only [memByte, PhysicalMemory.read, hb]

theorem suffix_saved_word {s u t : RamState}
    (rsp : (Operand.reg 4 : Operand 64).read u = scratch s)
    (effect : (setupSuffixEffect u).Holds u t) :
    (Operand.mem (stackPtr s - 8) : Operand 64).read t =
      (Operand.mem (stackPtr s - 8) : Operand 64).read u := by
  have addr : stackPtr s - 8 = scratch s + 32 := by
    simp only [scratch, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have apart (k : BitVec 64) (hk : k ∈ ([0, 8, 16, 24] : List (BitVec 64))) :
      RangeApart (scratch s + k) 8 (scratch s + 32) 8 := by
    have h : OffsetsApart k 8 32 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> (unfold OffsetsApart; decide +kernel)
    exact fun i hi j hj => h.ne (scratch s) hi hj (by decide)
  rw [addr]
  apply memLoad_congr
  intro i hi
  have hb : t.external[scratch s + 32 + BitVec.ofNat 64 i]? =
      u.external[scratch s + 32 + BitVec.ofNat 64 i]? := by
    apply effect.agrees.byte
    intro c hc ha
    simp only [setupSuffixEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    all_goals
      obtain ⟨j, hj, heq⟩ := ha
      rw [rsp] at heq
    · exact apart 0 (by simp) j hj i hi heq.symm
    · exact apart 8 (by simp) j hj i hi heq.symm
    · exact apart 16 (by simp) j hj i hi heq.symm
    · exact apart 24 (by simp) j hj i hi heq.symm
  simp only [memByte, PhysicalMemory.read, hb]

theorem setup_effect_of_parts [Bindings] {s u t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x114380 32 32 128)
    (prepare : (prepareEffect s).Holds s u)
    (suffix : (setupSuffixEffect u).Holds u t) : (setupEffect s).Holds s t := by
  have hp := prepare.writes
  change _ ∧ _ ∧ _ ∧ _ at hp
  rcases hp with ⟨rsp, r8, rbx, saved⟩
  have rsi : (Operand.reg 6 : Operand 64).read u = s.regValue .rsi :=
    prepare.agrees.read (n := 64) (r := 6) (by simp [prepareEffect, Effect.components])
  have hs := suffix.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hs
  rcases hs with ⟨rax, rcx, si, di, word0, word8, word16, word24⟩
  change (Operand.reg 4 : Operand 64).read u = scratch s at rsp
  have source0 := prepare_source_word pre prepare (offset := 0) (by decide)
  have source8 := prepare_source_word pre prepare (offset := 8) (by decide)
  have source16 := prepare_source_word pre prepare (offset := 16) (by decide)
  have source24 := prepare_source_word pre prepare (offset := 24) (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at rsp rsi
  simp only [Write.AllHold, BitVec.ofNat_eq_ofNat, rsp, rsi, BitVec.add_zero]
    at rax di word0 word8 word16 word24
  simp only [BitVec.add_zero] at source0
  refine ⟨suffix.rip, ?_, ?_, ?_⟩
  · change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨rax.trans source0, rcx, ?_, ?_, si, di, ?_,
      (suffix_saved_word rsp suffix).trans saved,
      word0.trans source0, word8.trans source8, word16.trans source16, word24.trans source24⟩
    · exact (suffix.agrees.read (n := 64) (r := 3)
        (by simp [setupSuffixEffect, Effect.components])).trans rbx
    · exact (suffix.agrees.read (n := 64) (r := 4)
        (by simp [setupSuffixEffect, Effect.components])).trans rsp
    · exact (suffix.agrees.read (n := 64) (r := 8)
        (by simp [setupSuffixEffect, Effect.components])).trans r8
  · have hf := suffix.agrees.rflags (by simp [setupSuffixEffect, Effect.components]) (by simp [setupSuffixEffect, Effect.components])
    change (StatusFlagsOutcome.ofStatusFlags (subSpec (stackPtr s - 8) (32 : BitVec 64)).2).Allows
      (StatusFlags.ofRFLAGS t.RFLAGS)
    rw [hf]
    exact prepare.flags
  · apply (prepare.agrees.trans suffix.agrees).mono
    have rspGPR := rsp
    change u.GPR[gprIndex (4#5)] = scratch s at rspGPR
    simp [prepareEffect, setupSuffixEffect, setupEffect, Effect.components, rspGPR]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
