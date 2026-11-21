import P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish.Instructions
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

open P256.Proofs.Program (CalleePre readyToStep programLoaded_codeIn programText_slice)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {p : BitVec 64}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : Stage s t boundary)
    (rip : t.RIP = p) : OutputPre p t := by
  refine ⟨rip, ?_, ?_⟩
  · intro off ho
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rbx + off) 8
    rw [state.output]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    all_goals exact (output_writable pre state.toFrameState).add _ (len := 8) (by decide)
  · intro off ho codeOffset len bound
    change RangeApart (t.regValue .rbx + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) len
    rw [state.output]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    all_goals exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := output_code pre bound) _ (len := 8) (by decide)

theorem reject [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : Stage s t boundary)
    (rip : t.RIP = 0x10fb90) (tag : t.regValue .r14 = 1) :
    ∃ u, Stage s u boundary ∧ u.RIP = 0x10fb96 ∧
      loadBytes u.external (s.regValue .rdi) 8 = .ok (1 : BitVec 64) := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := reject_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfb90 rejectBytes
      (by decide) (by decide +kernel)) (output_pre pre state rip)
  have ag : AgreesExcept [.mem (s.regValue .rdi) 8, .reg 0, .rip] t u := by
    have output : t.GPR[↑(gprIndex 3#5)] = s.regValue .rdi := state.output
    simpa [rejectEffect, Effect.components, Write.component, Operand.component,
      Operand.read_reg64, output] using effect.agrees
  have writes : WritesWithin [.mem (s.regValue .rdi) 8, .reg 0, .rip]
      #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨registerRegion s .rdi 40, by simp, output_contains pre (len := 8) (offset := 0) (by decide)
        (by simpa only [BitVec.add_zero] using ha)⟩
    · exact ha.elim
    · exact ha.elim
  have st := state.after pre run ready ag writes
    ((ag.read (n := 64) (r := 4) (by simp)).trans state.rsp) (by simp)
  have word : memLoad u.external (s.regValue .rdi) 64 = 1 := by
    have h := effect.writes.1
    change memLoad u.external (t.regValue .rbx) 64 = t.regValue .r14 at h
    simpa only [state.output, tag] using h
  have bytes := Bytes.of_memLoad (n := 64) (by
    intro i hi
    exact (output_writable pre st.toFrameState).mem i (by omega))
  rw [word] at bytes
  exact ⟨u, st, effect.rip, bytes.loadBytes64⟩

theorem accept [Bindings] {s t : RamState} {boundary : ReturnBoundary} {value : Nat}
    (pre : CalleePre s boundary 0x10fa20 32 40 288) (state : Stage s t boundary)
    (rip : t.RIP = 0x10fb7d) (bound : value < 2^256)
    (limb0 : t.regValue .r15 = BitVec.ofNat 64 value)
    (limb1 : t.regValue .r12 = BitVec.ofNat 64 (value / 2^64))
    (limb2 : t.regValue .r13 = BitVec.ofNat 64 (value / 2^128))
    (limb3 : t.regValue .rbp = BitVec.ofNat 64 (value / 2^192)) :
    ∃ u, Stage s u boundary ∧ u.RIP = 0x10fb96 ∧
      loadBytes u.external (s.regValue .rdi) 8 = .ok (0 : BitVec 64) ∧
      Nat256At u (s.regValue .rdi + 8) value := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := accept_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfb7d acceptBytes
      (by decide) (by decide +kernel)) (output_pre pre state rip)
  have ag : AgreesExcept [.mem (s.regValue .rdi + 8) 8, .mem (s.regValue .rdi + 16) 8,
      .mem (s.regValue .rdi + 24) 8, .mem (s.regValue .rdi + 32) 8,
      .reg 14, .mem (s.regValue .rdi) 8, .reg 0, .flags, .rip] t u := by
    have output : t.GPR[↑(gprIndex 3#5)] = s.regValue .rdi := state.output
    simpa [acceptEffect, Effect.components, Write.component, Operand.component,
      Operand.read_reg64, output] using effect.agrees
  have writes : WritesWithin [.mem (s.regValue .rdi + 8) 8, .mem (s.regValue .rdi + 16) 8,
      .mem (s.regValue .rdi + 24) 8, .mem (s.regValue .rdi + 32) 8,
      .reg 14, .mem (s.regValue .rdi) 8, .reg 0, .flags, .rip]
      #v[registerRegion s .rdi 40, Program.ScalarFrame.workRegion s 288] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨registerRegion s .rdi 40, by simp, ?_⟩
    · exact output_contains pre (len := 8) (offset := 8) (by decide) ha
    · exact output_contains pre (len := 8) (offset := 16) (by decide) ha
    · exact output_contains pre (len := 8) (offset := 24) (by decide) ha
    · exact output_contains pre (len := 8) (offset := 32) (by decide) ha
    · exact output_contains pre (len := 8) (offset := 0) (by decide) (by simpa only [BitVec.add_zero] using ha)
  have st := state.after pre run ready ag writes
    ((ag.read (n := 64) (r := 4) (by simp)).trans state.rsp) (by simp)
  have values := effect.writes
  change memLoad u.external (t.regValue .rbx + 8) 64 = t.regValue .r15 ∧
    memLoad u.external (t.regValue .rbx + 16) 64 = t.regValue .r12 ∧
    memLoad u.external (t.regValue .rbx + 24) 64 = t.regValue .r13 ∧
    memLoad u.external (t.regValue .rbx + 32) 64 = t.regValue .rbp ∧
    u.regValue .r14 = 0 ∧ memLoad u.external (t.regValue .rbx) 64 = 0 ∧
    u.regValue .rax = t.regValue .rbx at values
  rw [state.output, limb0, limb1, limb2, limb3] at values
  have bytes := Bytes.of_memLoad (n := 64) (by
    intro i hi
    exact (output_writable pre st.toFrameState).mem i (by omega))
  rw [values.2.2.2.2.2.1] at bytes
  refine ⟨u, st, effect.rip, bytes.loadBytes64, ?_⟩
  apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs bound
    ((output_writable pre st.toFrameState).add 8 (len := 32) (by decide)).mem
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · simpa only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using values.1
  · change memLoad u.external (s.regValue .rdi + 8#64 + 8#64) 64 = _
    simpa [BitVec.add_assoc] using values.2.1
  · change memLoad u.external (s.regValue .rdi + 8#64 + 16#64) 64 = _
    simpa [BitVec.add_assoc] using values.2.2.1
  · change memLoad u.external (s.regValue .rdi + 8#64 + 24#64) 64 = _
    simpa [BitVec.add_assoc] using values.2.2.2.1

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Finish
