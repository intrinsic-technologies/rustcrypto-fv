import P256.Proofs.Signing.Core.Initialize.State
import P256.Proofs.Signing.Core.Initialize.Arguments
import P256.Proofs.Signing.Core.Initialize.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat)

theorem arguments_entry [Bindings] {s t : RamState} {boundary : ReturnBoundary} {secret : Nat}
    (pre : SignPre s boundary)
    (state : Encoded s t secret) (rip : t.RIP = 0x10ca39) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10ca68 ∧ CallInput s u secret := by
  have blockPre : ArgumentsPre t := by
    refine ⟨rip, ?_, ?_⟩
    · intro off member
      have eq : off = 88 := by simpa using member
      subst off
      exact writable pre state.frame (by decide) (by decide)
    · intro off member offset len bound
      have eq : off = 88 := by simpa using member
      subst off
      exact ScalarFrame.stack_code pre.toCalleePre (scalarFrame state.frame) (by decide) (by decide) bound
  obtain ⟨fuel, u, run, ready, _, effect⟩ := arguments_block boundary pre.outerBoundary t
    (readyToStep state.frame.machine state.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.frame.loaded) 0xca39 argumentsBytes
      (by decide) (by decide +kernel)) blockPre
  have agrees : AgreesExcept [.reg 0, .reg 7, .reg 15, .reg 2, .reg 6,
      .mem (frameBase s + 88) 8, .reg 1, .reg 8, .reg 9, .reg 14, .rip] t u := by
    simpa only [argumentsEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component, state.frame.rsp] using effect.agrees
  have writes : LocalWrites s [.reg 0, .reg 7, .reg 15, .reg 2, .reg 6,
      .mem (frameBase s + 88) 8, .reg 1, .reg 8, .reg 9, .reg 14, .rip] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨88 + i, by omega, ?_⟩
    simp only [BitVec.add_assoc, BitVec.ofNat_add]
    rfl
  have copy (offset : Nat) (bound : offset < 2288) (apart : offset < 88 ∨ 96 ≤ offset) :
      u.external[frameBase s + BitVec.ofNat 64 offset]? =
        t.external[frameBase s + BitVec.ofNat 64 offset]? := by
    apply agrees.memory
    intro c hc cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    obtain ⟨i, hi, he⟩ := cover
    have eqv : BitVec.ofNat 64 (88 + i) = BitVec.ofNat 64 offset := by
      apply (BitVec.add_right_inj (frameBase s)).mp
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact he.symm
    have eqn := congrArg BitVec.toNat eqv
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 88 + i < 2^64),
      Nat.mod_eq_of_lt (by omega : offset < 2^64)] at eqn
    omega
  have word (offset : Nat) (bound : offset + 8 ≤ 2288)
      (apart : offset + 8 ≤ 88 ∨ 96 ≤ offset) :
      (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read u =
        (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read t := by
    apply memLoad_congr
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, copy (offset + i) (by omega) (by omega)]
  have result := effect.writes
  change u.regValue .rax = stackPtr t + 272 ∧ u.regValue .rdi = stackPtr t + 2160 ∧
    u.regValue .r15 = 32 ∧ u.regValue .rdx = 32 ∧ u.regValue .rsi = t.regValue .rbp ∧
    (Operand.mem (stackPtr t + 88) : Operand 64).read u = t.regValue .r13 ∧
    u.regValue .rcx = t.regValue .r13 ∧ u.regValue .r8 = t.regValue .r12 ∧
    u.regValue .r9 = t.regValue .r14 ∧ u.regValue .r14 = stackPtr t + 2160 at result
  rw [state.frame.rsp, state.r13, state.rbp, state.r12, state.r14] at result
  rcases result with ⟨rax, rdi, r15, rdx, rsi, digest, rcx, r8, r9, r14⟩
  refine ⟨fuel, u, run, effect.rip, after_effect pre state.frame ready agrees writes (by simp),
    (word 72 (by decide) (.inl (by decide))).trans state.output,
    (word 80 (by decide) (.inl (by decide))).trans state.secret,
    digest, ?_, ?_, rax, rdi, rsi, rdx, rcx, r8, r9, ?_, ?_, ?_, r14, r15⟩
  · refine ⟨state.order.1, ?_⟩
    intro i hi
    have copied := copy (272 + i) (by omega) (.inr (by omega))
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at copied
    exact copied.trans (state.order.2 i hi)
  · intro i hi
    have copied := copy (528 + i) (by omega) (.inr (by omega))
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at copied
    exact copied.trans (state.bytes i hi)
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans state.rbx
  · exact (agrees.read (n := 64) (r := 12) (by simp)).trans state.r12
  · exact (agrees.read (n := 64) (r := 5) (by simp)).trans state.rbp

end P256.Proofs.Signing.Core.Initialize
