import P256.Proofs.Signing.Core.Initialize.State
import P256.Proofs.Signing.Core.Initialize.LoopSetup
import P256.Proofs.Common.Instructions.CmovAboveEqual
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions
open NextNonce (scalarFrame coreFrame base_add base_nat)
open SecretKeyFromBytes.Scalar (Nat256At)

theorem select_length [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    (pre : SignPre s boundary) (input : Initialized s t state) (rip : t.RIP = 0x10ca73) :
    ∃ u, Advances boundary 2 t u ∧ Initialized s u state ∧ u.RIP = 0x10ca7b := by
  obtain ⟨a, run1, ready1, e1⟩ := (cmp_r64_imm8_effect_step 0x10ca73 0x49 0xfc 32
      (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep input.frame.machine input.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.frame.loaded) 0xca73 _
      (by decide) (by decide +kernel)) rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xca77 (by decide)))
  change (cmpR64Imm8Effect 0x10ca73 12 32 t).Holds t a at e1
  have mem1 : a.external = t.external := e1.agrees.external (by simp [Component.Covers])
  obtain ⟨u, run2, ready2, e2⟩ := (cmovae_r64_r64_effect_step 0x10ca77 0x4d 0x43 0xe7
      (by simp [RexWPrefix]) rfl rfl).advances ready1
    (programText_slice ((programLoaded_codeIn input.frame.loaded).of_external_eq mem1) 0xca77 _
      (by decide) (by decide +kernel)) e1.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xca7b (by decide)))
  change (cmovR64R64Effect 0x10ca77 3 12 15 a).Holds a u at e2
  have agrees : AgreesExcept [.reg 12, .flags, .rip] t u := by
    apply (e1.agrees.trans e2.agrees).mono
    simp [cmpR64Imm8Effect, cmovR64R64Effect, Effect.components]
  have memory : u.external = t.external := agrees.external (by simp [Component.Covers])
  have a12 : a.regValue .r12 = 32 :=
    (e1.agrees.read (n := 64) (r := 12) (by simp)).trans input.r12
  have a15 : a.regValue .r15 = 32 :=
    (e1.agrees.read (n := 64) (r := 15) (by simp)).trans input.r15
  have u12 : u.regValue .r12 = 32 := by
    have h := e2.writes
    change u.regValue .r12 = (if condHolds 3 (StatusFlags.ofRFLAGS a.RFLAGS) then
      a.regValue .r15 else a.regValue .r12) at h
    simpa only [a12, a15, ite_self] using h
  refine ⟨u, run1.trans run2, ⟨?_, ?_, ?_, ?_, ?_, u12, ?_, ?_, ?_⟩, e2.rip⟩
  · exact after_effect pre input.frame ready2 agrees
      (by
        intro c hc a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> exact ha.elim) (by simp)
  · change memLoad u.external _ 64 = _
    rw [memory]
    exact input.output
  · change memLoad u.external _ 64 = _
    rw [memory]
    exact input.secret
  · change memLoad u.external _ 64 = _
    rw [memory]
    exact input.digest
  · simpa only [Nonce.GeneratorAt, Nonce.DrbgAt, Nat256At, memory] using input.generator
  · exact (agrees.read (n := 64) (r := 5) (by simp)).trans input.rbp
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans input.r14
  · exact (agrees.read (n := 64) (r := 15) (by simp)).trans input.r15

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    (pre : SignPre s boundary) (input : Initialized s t state) (rip : t.RIP = 0x10ca73) :
    ∃ fuel u, Advances boundary fuel t u ∧ Loop s u state ∧ u.RIP = 0x10caa5 := by
  obtain ⟨a, prefixRun, selected, rip1⟩ := select_length pre input rip
  have blockPre : LoopSetupPre a := by
    refine ⟨rip1, ?_, ?_⟩
    · exact writable pre selected.frame (by decide) (by decide)
    · intro offset len bound
      exact ScalarFrame.stack_code pre.toCalleePre (scalarFrame selected.frame) (by decide) (by decide) bound
  obtain ⟨fuel, u, run, ready, _, effect⟩ := loop_setup_correct boundary pre.outerBoundary a
    (readyToStep selected.frame.machine selected.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn selected.frame.loaded) 0xca7b loopSetupBytes
      (by decide) (by decide +kernel)) blockPre
  have agrees : AgreesExcept [.mem (frameBase s + 96) 8, .reg 3, .reg 13, .reg 15, .rip] a u := by
    simpa only [loopSetupEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component, selected.frame.rsp]
      using effect.agrees
  have writes : LocalWrites s [.mem (frameBase s + 96) 8, .reg 3, .reg 13, .reg 15, .rip] := by
    intro c hc address ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨96+i, by omega, ?_⟩
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    all_goals exact ha.elim
  have copy (offset : Nat) (bound : offset < 2288) (apart : offset < 96 ∨ 104 ≤ offset) :
      u.external[frameBase s + BitVec.ofNat 64 offset]? =
        a.external[frameBase s + BitVec.ofNat 64 offset]? := by
    apply agrees.memory
    intro c hc cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨i, hi, eq⟩ := cover
      have val : BitVec.ofNat 64 offset = BitVec.ofNat 64 (96+i) := by
        apply (BitVec.add_right_inj (frameBase s)).mp
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        exact eq
      have hn := congrArg BitVec.toNat val
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
        Nat.mod_eq_of_lt (by omega : 96+i < 2^64)] at hn
      omega
    all_goals exact cover.elim
  have word (offset : Nat) (bound : offset + 8 ≤ 2288)
      (apart : offset + 8 ≤ 96 ∨ 104 ≤ offset) :
      (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read u =
        (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read a := by
    apply memLoad_congr
    intro i hi
    change (u.external[_]?).getD 0 = (a.external[_]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, copy (offset+i) (by omega) (by omega)]
  have values := effect.writes
  change (Operand.mem (stackPtr a + 96) : Operand 64).read u = a.regValue .r12 ∧
    u.regValue .rbx = stackPtr a + 40 ∧ u.regValue .r13 = stackPtr a + 432 ∧
    u.regValue .r15 = stackPtr a + 1328 at values
  rw [selected.frame.rsp, selected.r12] at values
  rcases values with ⟨length, rbx, r13, r15⟩
  refine ⟨2+fuel, u, prefixRun.trans run,
    ⟨after_effect pre selected.frame ready agrees writes (by simp),
      ⟨(word 72 (by decide) (.inl (by decide))).trans selected.output,
        (word 80 (by decide) (.inl (by decide))).trans selected.secret,
        (word 88 (by decide) (.inl (by decide))).trans selected.digest, length⟩,
      ?_, (agrees.read (n := 64) (r := 5) (by simp)).trans selected.rbp,
      rbx, r13, (agrees.read (n := 64) (r := 14) (by simp)).trans selected.r14, r15⟩,
      effect.rip⟩
  apply selected.generator.copy
  · intro i hi
    have copied := copy (2160+i) (by omega) (.inr (by omega))
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at copied
    exact copied
  · refine ⟨selected.generator.2.1.1, fun i hi => ?_⟩
    have copied := copy (272+i) (by omega) (.inr (by omega))
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at copied
    exact copied.trans (selected.generator.2.1.2 i hi)

end P256.Proofs.Signing.Core.Initialize
