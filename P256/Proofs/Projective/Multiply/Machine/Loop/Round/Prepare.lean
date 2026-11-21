import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Stage
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.Double
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.FirstArguments
import P256.Proofs.Projective.Multiply.Machine.Loop.Round.AfterDouble

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Round

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem remaining_sub {n : Nat} (bound : n < 64) :
    BitVec.ofNat 64 (64-n) - 1 = BitVec.ofNat 64 (63-n) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  congr 1
  omega

theorem prepare_round [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {n : Nat} (pre : Pre s boundary)
    (state : LoopState s t table n) (bound : n < 64) :
    ∃ fuel u, Advances boundary fuel t u ∧
      RoundState s u n 0x103380 336
        (ProjectiveLoop.double4 (ProjectiveLoop.accumulator table (digits s) n)) ∧
      u.regValue .rax = stackPtr s - 144 := by
  obtain ⟨a, v, runV, readyV, _, effectV⟩ := firstArguments_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x3340 firstArgumentsBytes
      (by decide) (by decide +kernel))
    ⟨by simpa only [bound, ite_true] using state.rip,
      stack_writable pre.toCalleePre state.toFrameState (by decide) (by decide) (by decide),
      stack_code pre.toCalleePre state.toFrameState (offset := 8) (len := 8)
        (codeOffset := 0x3340) (codeLen := 11) (by decide) (by decide) (by decide)⟩
  have addrV : stackPtr t + 8 = stackPtr s - 368 :=
    scalar_stack_address (frameOffset := 376) state.rsp (by decide) (by decide)
  have frameV : AgreesExcept [.mem (stackPtr s-368) 8, .reg 7, .reg 5, .rip] t v := by
    have h := effectV.agrees
    simp only [firstArgumentsEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.cons_append, List.nil_append, Nat.reduceDiv] at h
    change AgreesExcept [.mem (stackPtr t+8) 8, .reg 7, .reg 5, .rip] t v at h
    rwa [addrV] at h
  have writesV : ∀ c ∈ [Component.mem (stackPtr s-368) 8, .reg 7, .reg 5, .rip],
      ∀ x, c.Covers x → (Component.mem (stackPtr s-368) 8).Covers x := by
    intro c hc x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> first | exact hx | exact hx.elim
  have sv := after_single_write pre state.toFrameState readyV frameV writesV
    (by decide) (by decide) (by simp)
  have valuesV : (Operand.mem (stackPtr t+8) : Operand 64).read v = t.regValue .r9 ∧
      v.regValue .rdi = t.regValue .r13 ∧ v.regValue .rbp = t.regValue .rax := effectV.writes
  have pointV := state.value.of_bytes_eq (fun i hi => stack_bytes_of_agrees pre frameV writesV
    (by decide) (by decide) (by decide) (by decide) (by decide) hi)
  have r13V : v.regValue .r13 = stackPtr s-336 :=
    (frameV.read (n := 64) (r := 13) (by simp)).trans state.r13
  obtain ⟨b, doubled⟩ := double_four pre sv effectV.rip
    (valuesV.2.1.trans state.r13) r13V pointV
  have sb := doubled.toFrameState
  obtain ⟨c, u, runU, readyU, _, effectU⟩ := afterDouble_correct boundary pre.outerBoundary b
    (readyToStep sb.machine sb.bindingsSupported)
    (programText_slice (programLoaded_codeIn sb.loaded) 0x3368 afterDoubleBytes
      (by decide) (by decide +kernel))
    ⟨doubled.rip, stack_writable pre.toCalleePre sb (by decide) (by decide) (by decide),
      stack_code pre.toCalleePre sb (offset := 32) (len := 8)
        (codeOffset := 0x3368) (codeLen := 24) (by decide) (by decide) (by decide)⟩
  have addrU : stackPtr b + 32 = stackPtr s-344 :=
    scalar_stack_address (frameOffset := 376) sb.rsp (by decide) (by decide)
  have frameU : AgreesExcept [.reg 0, .mem (stackPtr s-344) 8,
      .reg 15, .reg 3, .reg 12, .flags, .rip] b u := by
    have h := effectU.agrees
    simp only [afterDoubleEffect, Effect.components, List.map_cons, List.map_nil, Write.component,
      Operand.component, List.cons_append, List.nil_append, Nat.reduceDiv] at h
    change AgreesExcept [.reg 0, .mem (stackPtr b+32) 8,
      .reg 15, .reg 3, .reg 12, .flags, .rip] b u at h
    rwa [addrU] at h
  have writesU : ∀ c ∈ [Component.reg 0, .mem (stackPtr s-344) 8,
      .reg 15, .reg 3, .reg 12, .flags, .rip],
      ∀ x, c.Covers x → (Component.mem (stackPtr s-344) 8).Covers x := by
    intro c hc x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hx | exact hx.elim
  have su := after_single_write pre sb readyU frameU writesU (by decide) (by decide) (by simp)
  have valuesU : u.regValue .rax = b.regValue .rbp ∧
      (Operand.mem (stackPtr b+32) : Operand 64).read u = b.regValue .r15-1 ∧
      u.regValue .r15 = b.regValue .rbx ∧ u.regValue .rbx = 0 ∧
      u.regValue .r12 = stackPtr b+136 := effectU.writes
  have rbpB : b.regValue .rbp = stackPtr s-144 :=
    (doubled.registers .rbp (by simp)).trans (valuesV.2.2.trans state.rax)
  have r15B : b.regValue .r15 = BitVec.ofNat 64 (64-n) :=
    (doubled.registers .r15 (by simp)).trans
      ((frameV.read (n := 64) (r := 15) (by simp)).trans state.r15)
  have rbxB : b.regValue .rbx = s.regValue .rsi :=
    (doubled.registers .rbx (by simp)).trans
      ((frameV.read (n := 64) (r := 3) (by simp)).trans state.rbx)
  have keepV (offset : Nat) (ho : offset ≤ 376) (apart : 376 ≤ offset ∨ offset+8 ≤ 368) :=
    stack_read_of_agrees (offset := offset) (n := 64) pre frameV writesV
      (by decide) (by decide) (by omega) (by omega) apart
  have keepU (offset : Nat) (ho : offset ≤ 376) (apart : 352 ≤ offset) :=
    stack_read_of_agrees (offset := offset) (n := 64) pre frameU writesU
      (by decide) (by decide) (by omega) (by omega) (Or.inl apart)
  have keep (offset : Nat) (ho : offset ≤ 376) (lo : 352 ≤ offset)
      (apart : 376 ≤ offset ∨ offset+8 ≤ 368) :=
    (keepU offset ho lo).trans ((doubled.read ho (by omega) (Or.inr (by omega))).trans
      (keepV offset ho apart))
  have cursor : (Operand.mem (stackPtr s-368) : Operand 64).read u =
      s.regValue .rcx + BitVec.ofNat 64 (63-n) := by
    change (Operand.mem (stackPtr s - (368#64)) : Operand 64).read u = _
    have cursorV : (Operand.mem (stackPtr s-368#64) : Operand 64).read v = t.regValue .r9 :=
      (congrArg (fun x => (Operand.mem x : Operand 64).read v) addrV.symm).trans valuesV.1
    rw [keepU 368 (by decide) (by decide), doubled.read (offset := 368)
      (by decide) (by decide) (by decide), cursorV, state.r9]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, remaining_sub bound]
  obtain ⟨d, runB⟩ := doubled.execution
  refine ⟨a+d+c, u, (runV.trans runB).trans runU, ?_, valuesU.1.trans rbpB⟩
  refine ⟨su, bound, effectU.rip, ?_, valuesU.2.2.2.1, ?_, ?_, ?_, ?_,
    valuesU.2.2.1.trans rbxB, ?_, ?_, ?_, cursor, ?_⟩
  · exact doubled.value.of_bytes_eq (fun i hi => stack_bytes_of_agrees pre frameU writesU
      (by decide) (by decide) (by decide) (by decide) (by decide) hi)
  · exact (frameU.read (n := 64) (r := 5) (by simp)).trans rbpB
  · exact valuesU.2.2.2.2.trans
      (scalar_stack_address (frameOffset := 376) sb.rsp (by decide) (by decide))
  · exact (frameU.read (n := 64) (r := 13) (by simp)).trans
      ((doubled.registers .r13 (by simp)).trans r13V)
  · exact (frameU.read (n := 64) (r := 14) (by simp)).trans
      ((doubled.registers .r14 (by simp)).trans
        ((frameV.read (n := 64) (r := 14) (by simp)).trans state.r14))
  · exact (keep 376 (by decide) (by decide) (by decide)).trans state.count
  · exact (keep 360 (by decide) (by decide) (by decide)).trans state.output
  · exact (keep 352 (by decide) (by decide) (by decide)).trans state.table
  · rw [← addrU, valuesU.2.1, r15B]
    exact remaining_sub bound

end P256.Proofs.Projective.Multiply.Machine.Loop.Round
