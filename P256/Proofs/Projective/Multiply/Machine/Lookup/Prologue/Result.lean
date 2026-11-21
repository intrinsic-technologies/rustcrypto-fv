import P256.Proofs.Projective.Multiply.Machine.Lookup.State
import P256.Proofs.Projective.Multiply.Machine.Lookup.Prologue.Initialize
import P256.Proofs.Projective.Multiply.Machine.Lookup.Prologue.Digit

set_option autoImplicit false

open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Initialization

set_option maxHeartbeats 800000 in
theorem prologue [Bindings] {s : RamState} {boundary : ReturnBoundary} {digit : BitVec 8}
    (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (hdigit : (s.regValue .rdx).setWidth 8 = digit) :
    ∃ fuel t, Advances boundary fuel s t ∧ ScanState s t digit := by
  obtain ⟨n, u, run, state⟩ := initialize_correct pre
  obtain ⟨m, t, run', ready, _, effect⟩ := digit_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x44d3 digitBytes
      (by decide) (by decide +kernel))
    ⟨state.rip, stack_writable pre state.toFrameState (offset := 12) (by decide) (by decide),
      stack_code pre state.toFrameState (offset := 12) (len := 4) (codeOffset := 0x44d3)
        (by decide) (by decide)⟩
  have address : stackPtr u + 12 = stackPtr s - 348 := stack_address state.rsp (by decide)
  have agr : AgreesExcept [.reg 14, .mem (stackPtr s - 348) 4, .reg 0, .reg 15, .flags, .rip] u t := by
    have h := effect.agrees
    simp only [digitEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.cons_append, List.nil_append, Nat.reduceDiv] at h
    exact (congrArg (fun a : BitVec 64 =>
      AgreesExcept [.reg 14, .mem a 4, .reg 0, .reg 15, .flags, .rip] u t) address).mp h
  have writes : WritesWithin [.reg 14, .mem (stackPtr s - 348) 4, .reg 0, .reg 15, .flags, .rip]
      #v[registerRegion s .rdi 96, workRegion s] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s, by simp, work_contains pre (by decide) (by decide) ha⟩
  have state' := after pre state.toFrameState ready agr writes (by simp)
  have memory {offset len : Nat} (small : len ≤ 96) (apart : OffsetsApart (-348) 4 (-BitVec.ofNat 64 offset) len) :
      ∀ i < len, t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    apply agr.byte
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    rintro ⟨j, hj, he⟩
    apply OffsetsApart.ne apart (stackPtr s) hj hi (by omega)
    simpa [BitVec.sub_eq_add_neg] using he.symm
  have hw := effect.writes
  simp only [digitEffect, Write.AllHold] at hw
  refine ⟨n+m, t, run.trans run', state', effect.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact state.value.of_bytes_eq (memory (by decide) (by unfold OffsetsApart; decide +kernel))
  · have h := hw.2.2.2
    change t.regValue .r15 = _ at h
    rw [h]
    simp only [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, subSpec]
    have low : ((u.regValue .rdx).setWidth 32 |>.setWidth 64).setWidth 8 = digit := by
      simpa [state.rdx] using hdigit
    rw [low]
    exact abs_instructions digit
  · exact (agr.read (n := 64) (r := 13) (by simp)).trans state.r13
  · exact (agr.read (n := 64) (r := 5) (by simp)).trans state.rbp
  · exact hw.1.trans (stack_address state.rsp (by decide))
  · rw [← address]
    exact hw.2.1.trans (congrArg (BitVec.setWidth 32) state.rdx)
  · change memLoad t.external _ 64 = _
    apply Eq.trans _ state.output
    apply memLoad_congr
    intro i hi
    exact congrArg (Option.getD · 0)
      (memory (offset := 152) (len := 8) (by decide)
        (by unfold OffsetsApart; decide +kernel) i hi)

end P256.Proofs.Projective.Multiply.Machine.Lookup
